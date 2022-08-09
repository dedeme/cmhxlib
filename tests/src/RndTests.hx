// Copyright 14-Aug-2019 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

import dm.Test;
import dm.Rnd;
import dm.It;
import dm.Tp;

class RndTests {
  public static function run () {
    var t = new Test("Rnd");

    It.range(10).each(function (i) {
      t.yes(Rnd.i(4) >= 0 && Rnd.i(4) < 4);
    });

    It.range(10).each(function (i) {
      t.yes(
        Rnd.f(2, 4, 0) >= 0 && Rnd.f(2, 4, 0) <= 4
      );
    });

    It.range(10).each(function (i) {
      t.yes(
        Rnd.f(4, 8, 0) >= 4 && Rnd.f(4, 8, 0) <= 8
      );
    });

    var box = new Box(["a", "b", "c"]);
    var v = box.next();
    t.yes(v == "a" || v == "b" || v == "c");
    var v2 = box.next();
    t.yes(v != v2);
    t.yes(v2 == "a" || v2 == "b" || v2 == "c");
    var v3 = box.next();
    t.yes(v3 != v2 && v3 != v);
    t.yes(v3 == "a" || v3 == "b" || v3 == "c");
    v = box.next();
    t.yes(v == "a" || v == "b" || v == "c");
    v = box.next();
    t.yes(v == "a" || v == "b" || v == "c");
    v = box.next();
    t.yes(v == "a" || v == "b" || v == "c");
    v = box.next();
    t.yes(v == "a" || v == "b" || v == "c");

    box = Rnd.mkBox([new Tp("a", 2), new Tp("b", 1)]);
    v = box.next();
    t.yes(v == "a" || v == "b");
    v = box.next();
    t.yes(v == "a" || v == "b");
    v = box.next();
    t.yes(v == "a" || v == "b");
    v = box.next();
    t.yes(v == "a" || v == "b");
    v = box.next();
    t.yes(v == "a" || v == "b");
    v = box.next();
    t.yes(v == "a" || v == "b");
    v = box.next();
    t.yes(v == "a" || v == "b");

    //box = Rnd.mkBox([new Tp("a", 2), new Tp("b", 1)]);
    //var r = It.range(6).reduce("", (r, e) -> r + box.next());
    //trace(r);

    t.log();
  }
}
