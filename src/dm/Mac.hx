package dm;

using StringTools;
import haxe.macro.Context;
import haxe.macro.Expr;

/// Macros to easy JSON serialization.
class Mac {

  static function mkVKind (t: String): ComplexType {
    t = t.trim();
    final p1 = t.indexOf("<");
    if (p1 == -1) {
      return TPath({
        pack: [],
        name: t
      });
    }

    final p2 = t.length - 1;
    if (t.charAt(p2) != ">") {
      throw new haxe.Exception('Missing ">" in $t');
    }
    if (p2 - p1 < 2) {
      throw new haxe.Exception('Unexpected ">" in $t');
    }

    final sub = t.substring(p1 + 1, p2);
    final p3 = sub.indexOf("<");
    var a: Array<String>;
    if (p3 == -1) {
      a = sub.split(",");
    } else {
      a = sub.substring(0, p3).split(",");
      a[a.length - 1] = a[a.length - 1] + sub.substring(p3);
    }

    return TPath({
      params: a.map(e -> TPType(mkVKind(e))),
      pack: [],
      name: t.substring(0, p1).trim()
    });
  }

  static function getTypeName (tp: TypeParam): String {
    return switch (tp) {
      case TPType(ct):
        switch (ct) {
          case TPath (tp): tp.name;
          default: throw new haxe.Exception("Bad TPath");
        }
      default: throw new haxe.Exception("Bad TypeParam");
    }
  }

  static function getSubparam (tp: TypeParam, ix: Int): TypeParam {
    return switch (tp) {
      case TPType(ct):
        switch (ct) {
          case TPath (tp): tp.params[ix];
          default: throw new haxe.Exception("Bad TPath");
        }
      default: throw new haxe.Exception("Bad TypeParam");
    }
  }

  static function mkToRecursive (
    ftp: String -> haxe.macro.Type, tp: TypeParam
  ): Expr {
    final n = getTypeName(tp);
    return switch (n) {
      case "Bool": macro Js.wb(e);
      case "Int": macro Js.wi(e);
      case "Float": macro Js.wf(e);
      case "String": macro Js.ws(e);
      case "Option":
        final rec = mkToRecursive(ftp, getSubparam(tp, 0));
        macro switch (e) { case None: Js.wn(); case Some(e): ${rec} };
      case "Array":
        final rec = mkToRecursive(ftp, getSubparam(tp, 0));
        macro Js.wa(e.map(e -> ${rec}));
      case "Map":
        final rec = mkToRecursive(ftp, getSubparam(tp, 1));
        macro Js.wMap(e, e -> ${rec});
      default:
        switch (ftp(n)) {
          case TEnum(_):
            final n2 = "Js" + n;
            macro $i{n2}.to(e);
          default:
            macro e.toJs();
        }
    }
  }

  static function mkFromRecursive (
    ftp: String -> haxe.macro.Type, tp: TypeParam
  ): Expr {
    final n = getTypeName(tp);
    return switch (n) {
      case "Bool": macro e.rb();
      case "Int": macro e.ri();
      case "Float": macro e.rf();
      case "String": macro e.rs();
      case "Option":
        final rec = mkFromRecursive(ftp, getSubparam(tp, 0));
        macro e.isNull() ? None : Some((e -> ${rec})(e));
      case "Array":
        final rec = mkFromRecursive(ftp, getSubparam(tp, 0));
        macro e.ra().map(e -> ${rec});
      case "Map":
        final rec = mkFromRecursive(ftp, getSubparam(tp, 1));
        macro e.rMap(e -> ${rec});
      default:
        switch (ftp(n)) {
          case TEnum(_):
            final n2 = "Js" + n;
            macro $i{n2}.from(e);
          default:
            macro $i{n}.fromJs(e);
        }
    }
  }

  /// Generates a record-class with immutables fields.
  ///   fs: Fields in format "name: type".
  ///   serial: If is true, it will be created the following serialization
  ///           functions:
  ///             public static function fromJs (js: Js): Class {...}
  ///             and
  ///             public function toJs (): Js {...}
  ///
  /// EXAMPLE:
  ///   import dm.Mac;
  ///   import dm.Js;
  ///
  ///   enum TstType {A; B;}
  ///
  ///   @:build(dm.Mac.enumeration())
  ///   class JsTstType {}
  ///
  ///   @:build(dm.Mac.record([
  ///     "v0: Array<Array<Bool>>",
  ///     "v1: Int",
  ///     "v3: Map<String, Map<String, Int>>",
  ///     "v4: Array<TstType>",
  ///     "v5: Array<Tst>"
  ///     ], true))
  ///   class Tst {}
  ///
  /// NOTES:
  ///   - Only containers Array and Map<String, ?> are allowed.
  ///   - Functions 'setFields(value)' are defined for each field. They return
  ///             a new class with the field modified.
  ///   - To add instance functions, statics fields and statics functions
  ///             should be used 'using' importations.
  ///   - For serialization, classes other than Bool, Int, Float, String,
  ///     Array and Map<String, ?> must have defined the following functions:
  ///             public static function fromJs (js: Js): Class {...}
  ///             and
  ///             public function toJs (): Js {...}
  ///   - Only are serializable enum's without fields. A Class named
  ///     "Js" + EnumClassName (e.g. "JsBoxType") must be created. This
  ///     class must define:
  ///             public static function from (js: Js): EnumClass {...}
  ///             and
  ///             public static function to (e: EnumClass): Js {...}
  ///     To easy this work you can use the macro 'enumeration'.
  public macro static function record (
    fs: Array<String>, ?serial: Bool
  ): Array<Field> {
    if (serial == null) serial = false;

    final fields = [];
    for (f in fs) {
      final ps: Array<String> = f.split(":");
      final name = ps[0].trim();
      final tp = ps[1];
      fields.push({
        name: name,
        doc: null,
        meta: [],
        access: [APublic, AFinal],
        kind: FVar(mkVKind(tp), null),
        pos: Context.currentPos()
      });
    }

    final vars = fields.copy();

    fields.push({
      name: "new",
      doc: null,
      meta: [],
      access: [APublic],
      kind: FFun({
        ret: null,
        args: vars.map(v -> {
            name: v.name,
            type: switch (v.kind) {
                case FVar(t, _): t;
                default: throw new haxe.Exception("Unexpected field type");
              },
            meta: null,
            opt: null,
            value: null
          }),
        expr: macro $b{vars.map(v -> {
            final n = v.name;
            return macro this.$n = $i{n};
          })}
      }),
      pos: Context.currentPos()
    });

    for (f in fs) {
      final ps: Array<String> = f.split(":");
      final name = ps[0].trim();
      final tp = ps[1];
      final setName = "set" + name.charAt(0).toUpperCase() +
        name.substring(1, name.length);
      final cl = Context.getLocalClass().toString();
      fields.push({
        name: setName,
        doc: null,
        meta: [],
        access: [APublic],
        kind: FFun({
          args: [{name: "value"}],
          expr: {
            pos: Context.currentPos(),
            expr: EReturn ({
              pos: Context.currentPos(),
              expr: ENew({
                  pack: [],
                  name: cl
                },
                fs.map(f -> {
                  final name2 = f.split(":")[0].trim();
                  return name2 == name ? (macro value) : (macro $i{name2});
                })
              )
            })
          }
        }),
        pos: Context.currentPos()
      });
    }

    if (serial) {

      // TO JS -------------------------------------------------------

      final body: Array<Expr> = [];
      body.push(macro final a: Array<Js> = []);
      for (v in vars) {
        final n = v.name;
        switch (v.kind) {
          case FVar(ct, val):
            //if (val == null) body.push(macro a.push(Js.wn()));
            /*else*/ switch (ct) {
              case TPath(t): switch (t.name) {
                case "Bool": body.push(macro a.push(Js.wb($i{n})));
                case "Int": body.push(macro a.push(Js.wi($i{n})));
                case "Float": body.push(macro a.push(Js.wf($i{n})));
                case "String": body.push(macro a.push(Js.ws($i{n})));
                case "Option":
                  final rec = mkToRecursive(Context.getType, t.params[0]);
                  body.push(macro a.push(
                    switch ($i{n}) { case None: Js.wn(); case Some(e): ${rec} }
                  ));
                case "Array":
                  final rec = mkToRecursive(Context.getType, t.params[0]);
                  body.push(macro a.push(
                    Js.wa($i{n}.map(e -> ${rec}))
                  ));
                case "Map":
                  final rec = mkToRecursive(Context.getType, t.params[1]);
                  body.push(macro a.push(
                    Js.wMap($i{n}, e -> ${rec})
                  ));
                default:
                  switch (Context.getType(t.name)) {
                    case TEnum(_, _):
                      final t2 = "Js" + t.name;
                      body.push(macro a.push($i{t2}.to($i{n})));
                    default:
                      body.push(macro a.push($i{n}.toJs()));
                  }
              }
              default:
                throw new haxe.Exception("Bad ComplexType:\n" + Std.string(ct));
            }
          default:
            throw new haxe.Exception("Bad FieldType:\n" + Std.string(v.kind));
        }
      }
      body.push(macro return Js.wa(a));

      fields.push({
        name: "toJs",
        doc: null,
        meta: [],
        access: [APublic],
        kind: FFun({
          ret: mkVKind("Js"),
          args: [],
          expr: macro $b{body}
        }),
        pos: Context.currentPos()
      });

      // FROM JS -----------------------------------------------------

      final className = Context.getLocalClass().get().name;
      final body2: Array<Expr> = [];
      body2.push(macro final a = js.ra());

      final exps: Array<Expr> = [];
      for (i in 0...vars.length) {
        final v = vars[i];
        final n = v.name;
        exps.push(
          switch (v.kind) {
            case FVar(ct, _): switch (ct) {
              case TPath(t): switch (t.name) {
                case "Bool": macro a[$v{i}].rb();
                case "Int": macro a[$v{i}].ri();
                case "Float": macro a[$v{i}].rf();
                case "String": macro a[$v{i}].rs();
                case "Option":
                  final rec = mkFromRecursive(Context.getType, t.params[0]);
                  macro
                    a[$v{i}].isNull()
                      ? None
                      : Some((e -> ${rec})(a[$v{i}]));
                case "Array":
                  final rec = mkFromRecursive(Context.getType, t.params[0]);
                  macro a[$v{i}].ra().map(e -> ${rec});
                case "Map":
                  final rec = mkFromRecursive(Context.getType, t.params[1]);
                  macro a[$v{i}].rMap(e -> ${rec});
                default:
                  switch (Context.getType(t.name)) {
                    case TEnum(_, _):
                      final t2 = "Js" + t.name;
                      macro $i{t2}.from($i{n});
                    default:
                      macro $i{t.name}.fromJs($i{n});
                  }
              }
              default:
                throw new haxe.Exception("Bad ComplexType:\n" + Std.string(ct));
              }
            default:
              throw new haxe.Exception("Bad FieldType:\n" + Std.string(v.kind));
          }
        );
      }

      body2.push({
        pos: Context.currentPos(),
        expr: EReturn({
            pos: Context.currentPos(),
            expr: ENew({
                pack: [],
                name: className
              },
              exps
            )
          })
      });

      fields.push({
        name: "fromJs",
        doc: null,
        meta: [],
        access: [AStatic, APublic],
        kind: FFun({
          ret: mkVKind(className),
          args: [{
              type: mkVKind("Js"),
              name: "js"
            }],
          expr: macro $b{body2}
        }),
        pos: Context.currentPos()
      });

    }

    return fields;
  }

  /// Adds serialization to an enum.
  ///
  /// If the enumeration has the name "E", the class to serialize it must be
  /// called JsE, prefixing Js to name.
  ///
  /// For more information see comment in macro "record".
  ///
  /// EXAMPLE:
  ///   import dm.Mac;
  ///   import dm.Js;
  ///
  ///   enum TstType {A; B;}
  ///
  ///   @:build(dm.Mac.enumeration())
  ///   class JsTstType {}
  public macro static function enumeration (): Array<Field> {
    final className = Context.getLocalClass().get().name;
    if (!className.startsWith("Js") || className.length < 3)
      throw new haxe.Exception(
        'Bad name "$className". Use a name type "JsXxxx"'
      );
    final enumName = className.substring(2);

    final fields = [];
    switch (Context.getType(enumName)) {
      case TEnum(t, _):

        fields.push({
            name: "to",
            doc: null,
            meta: [],
            access: [AStatic, APublic],
            kind: FFun({
              ret: mkVKind("Js"),
              args: [{
                  type: mkVKind(enumName),
                  name: "en"
                }],
              expr: macro return Js.ws(Std.string(en))
            }),
            pos: Context.currentPos()
          });

        final body: Array<Expr> = [];
        body.push(macro final s = js.rs());
        for (n in t.get().names) {
          body.push(macro if (s == $v{n}) return $i{n});
        }
        body.push(macro throw new haxe.Exception("Bad value: " + s));

        fields.push({
            name: "from",
            doc: null,
            meta: [],
            access: [AStatic, APublic],
            kind: FFun({
              ret: mkVKind(enumName),
              args: [{
                  type: mkVKind("Js"),
                  name: "js"
                }],
              expr: macro $b{body}
            }),
            pos: Context.currentPos()
          });

        return fields;
      default:
        throw new haxe.Exception('"$enumName" not found or is not an enum');
    }
  }

}

