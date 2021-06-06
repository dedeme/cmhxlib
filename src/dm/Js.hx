// Copyright 15-Jun-2020 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

import haxe.Json;
import haxe.ds.Option;
#if js
import js.Syntax;
#end

/// Json utilities
class Js {

  var js: Dynamic;

  function new (js: Dynamic) {
    this.js = js;
  }

  function getType (): String {
    return Std.string(Type.typeof(js));
  }

  /**
      Trys Json.parse(s) and if it fails, throws a exception.
  **/
  public static function from (s: String): Js {
    try {
      return new Js(Json.parse(s));
    } catch (e: Dynamic) {
      throw Exc.illegalArgument('s = $s', "Json string", "Invalid Json");
    }
  }

  /**
      Returns Json.stringify(this).
  **/
  public function to (): String {
    return Json.stringify(this.js);
  }

  public static function wn (): Js {
    return new Js(null);
  }

  public static function wb (b: Bool): Js {
    return new Js(b);
  }

  public static function wi (i: Int): Js {
    return new Js(i);
  }

  public static function wf (f: Float): Js {
    return new Js(f);
  }

  public static function ws (s: String): Js {
    return new Js(s);
  }

  public static function wa (a:Array<Js>): Js {
    final jsa = [];
    for (e in a) jsa.push(e.js);
    return new Js(jsa);
  }

  public static function wo (o:Map<String, Js>): Js {
    #if js
    final fn1: () ->  Dynamic = () -> untyped Syntax.code("{}");
    final fn2: Dynamic -> String -> Js -> Void = (o, k, v) ->
      untyped Syntax.code("o[k]=v");

    final r = fn1();
    for (k in o.keys()) {
      final v = o[k];
      fn2(r, k , v.js);
    }
    return new Js(r);
    #else
    final r = new haxe.ds.StringMap<Js>();
    for (k in o.keys()) {
      final v = o[k];
      r.set(k, v.js);
    }
    return new Js(r);
    #end
  }

  /**
      Creates a Js (Array) from 'it' using fto to convert its elements.
  **/
  public static function wArray<T> (it: Iterable<T>, fto: T -> Js): Js {
    return wa(Lambda.map(it, fto));
  }

  /**
      Creates a Js (Object) from 'm' using fto to convert its values.
  **/
  public static function wMap<T> (m: Map<String, T>, fto: T -> Js): Js {
    final r = new Map<String, Js>();
    for (k => v in m)
      r.set(k, fto(v));
    return wo(r);
  }

  public function isNull (): Bool {
    return js == null;
  }

  public function rb (): Bool {
    try {
      return cast(js, Bool);
    } catch (e: String) {
      throw Exc.illegalArgument("js", "Bool", getType());
    }
  }

  public function ri (): Int {
    try {
      return cast(js, Int);
    } catch (e: String) {
      throw Exc.illegalArgument("js", "Int", getType());
    }
  }

  public function rf (): Float {
    try {
      return cast(js, Float);
    } catch (e: String) {
      throw Exc.illegalArgument("js", "Float", getType());
    }
  }

  public function rs (): String {
    try {
      return cast(js, String);
    } catch (e: String) {
      throw Exc.illegalArgument("js", "String", getType());
    }
  }

  public function ra (): Array<Js> {
    try {
      final a = [];
      for (e in cast(js, Array<Dynamic>)) a.push(new Js(e));
      return a;
    } catch (e: String) {
      throw Exc.illegalArgument("js", "Array<Js>", getType());
    }
  }

  public function ro (): Map<String, Js> {
    try {
      #if js
      final fn1: Dynamic -> Array<String> = (o) ->
        untyped Syntax.code("Object.keys(o)");
      final fn2: Dynamic -> String -> Dynamic = (o, k) ->
        untyped Syntax.code("o[k]");

      final obj:Dynamic = cast(js);
      final r = new Map<String, Js>();
      for (k in fn1(obj)) r.set(k, new Js(fn2(obj, k)));
      return r;
      #else
      final r = new Map<String, Js>();
      switch (Type.typeof(js)) {
        case TObject:
          for (k in Reflect.fields(js)) r.set(k, new Js(Reflect.field(js, k)));
        default:
          final m: haxe.ds.StringMap<Dynamic> = cast(js);
          for (k in m.keys()) r.set(k, new Js(m.get(k)));
      }
      return r;
      #end
    } catch (e: String) {
      throw Exc.illegalArgument("js", "Map<String, Js>", getType());
    }
  }

  /**
      Read an array whose elements can be deserialized with 'ffrom'.<p>
      If it fails, returns None.
  **/
  public function rArray<T> (ffrom: Js -> T): Array<T> {
    return ra().map(ffrom);
  }

  /**
      Read a Map whose values can be deserialized with 'ffrom'.<p>
      If it fails, returns None.
  **/
  public function rMap<T> (ffrom: Js -> T): Map<String, T> {
    final r = new Map<String, T>();
    for (k => v in ro()){
      r.set(k, ffrom(v));
    }
    return r;
  }

}
