// Copyright 15-Jun-2020 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

/// Utilities for managing paths with '/' as separator.
class Path {

  /// Returns the name of 'path'. For example:
  ///   name("") -> ""
  ///   name("ab.c") -> "ab.c"
  ///   name("d/ab.c") -> "ab.c"
  public static function name (path: String): String {
    final ix = path.lastIndexOf("/");
    if (ix != -1) {
      return path.substring(ix + 1);
    }
    return path;
  }

  /// Returns the parent of 'path'. For example:
  ///   parent("") -> ""
  ///   parent("ab.c") -> ""
  ///   parent("d/ab.c") -> "d"
  public static function parent (path: String): String {
    var ix = path.lastIndexOf("/");
    if (ix == -1) {
      ix = 0;
    }
    return path.substring(0, ix);
  }

  /// Returns the extension of 'path' (with '.'). For example:
  ///   extension("") -> ""
  ///   extension("ab.c") -> ".c"
  ///   extension("d/ab.c") -> ".c"
  public static function extension (path: String): String {
    final n = name(path);
    var ix = n.lastIndexOf(".");
    if (ix == -1) {
      ix = n.length;
    }
    return n.substring(ix);
  }

  /// Returns the name without extension of 'path'. For example:
  ///   onlyName("") -> ""
  ///   onlyName("ab.c") -> "ab"
  ///   onlyName("d/ab.c") -> "ab"
  public static function onlyName (path: String): String {
    final n = name(path);
    final ix = n.lastIndexOf(".");
    if (ix != -1) {
      return  n.substring(0, ix);
    }
    return n;
  }

  /// Concatenates several paths. For example:
  ///   cat([]) -> ""
  ///   cat(["a"]) -> "a"
  ///   cat(["/a", "b"]) -> "/a/b"
  public static function cat (ps: Array<String>): String {
    return It.join(It.from(ps).map(e -> e, e -> "/" + e ), "");
  }

  /// Returns the simplest expresion of path.
  public static function normalize (path: String): String {
    return haxe.io.Path.normalize(path);
  }

}
