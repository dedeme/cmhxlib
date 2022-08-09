// Copyright 09-Aug-2022 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

import dm.Test;
import dm.Rs;

class RsTests {
  public static function run() {
    function eq (r1: Result<Int>, r2: Result<Int>): Bool {
      return switch (r1) {
        case Ok(v1): switch (r2) {
          case Ok(v2): v1 == v2;
          default: false;
        }
        case Error(e1): switch (r2) {
          case Error(e2): e1 == e2;
          default: false;
        }
      }
    }
    final t = new Test("Rs");
    final err = Error("err");
    final ok = Ok(2);

    t.eq(Rs.fmap(err, x -> x*22), Error("err"), eq);
    t.eq(Rs.fmap(ok, x -> x*22), Ok(44), eq);

    t.eq(Rs.bind(err, x -> Ok(x*22)), Error("err"), eq);
    t.eq(Rs.bind(err, x -> Error("e2")), Error("err"), eq);
    t.eq(Rs.bind(ok, x -> Error("e2")), Error("e2"), eq);
    t.eq(Rs.bind(ok, x -> Ok(x*22)), Ok(44), eq);

    t.log();
  }
}
