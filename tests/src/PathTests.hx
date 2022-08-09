// Copyright 14-Aug-2019 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

import dm.Test;
import dm.Path;

class PathTests {
  public static function run() {
    final t = new Test("Path");

    t.eq(Path.name(""), "");
    t.eq(Path.name("/"), "");
    t.eq(Path.name("ab"), "ab");
    t.eq(Path.name("/ab.c"), "ab.c");
    t.eq(Path.name("cd/"), "");
    t.eq(Path.name("c/ab.c"), "ab.c");

    t.eq(Path.parent(""), "");
    t.eq(Path.parent("/"), "");
    t.eq(Path.parent("ab"), "");
    t.eq(Path.parent("/ab.c"), "");
    t.eq(Path.parent("cd/"), "cd");
    t.eq(Path.parent("cg/r/ab.c"), "cg/r");

    t.eq(Path.extension(""), "");
    t.eq(Path.extension("/"), "");
    t.eq(Path.extension("ab"), "");
    t.eq(Path.extension("/ab.c"), ".c");
    t.eq(Path.extension("cd/."), ".");
    t.eq(Path.extension("cg/r/ab."), ".");

    t.eq(Path.onlyName(""), "");
    t.eq(Path.onlyName("/"), "");
    t.eq(Path.onlyName("ab"), "ab");
    t.eq(Path.onlyName("/ab.c"), "ab");
    t.eq(Path.onlyName("cd/."), "");
    t.eq(Path.onlyName("cg/r/ab."), "ab");

    final p1 = "1";

    t.eq(Path.cat([]), "");
    t.eq(Path.cat([p1]), "1");
    t.eq(Path.cat([p1, "ab", "ab", "cd"]), "1/ab/ab/cd");
    t.eq(Path.cat(["/a", "b"]), "/a/b");

    t.eq(Path.normalize("/usr//local/..//lib"), "/usr/lib");

    t.log();
  }
}
