// Copyright 10-Aug-2019 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

import dm.Test;
import dm.Opt;

class OptTests {
  public static function run() {
    final t = new Test("Opt");
    final n = None;
    final s = Some(2);

    t.eq(Opt.get(n), null);
    t.eq(Opt.get(s), 2);

    t.eq(Opt.oget(n, 4), 4);
    t.eq(Opt.oget(s, 4), 2);

    //final err = Opt.eget(n);
    t.eq(Opt.eget(s), 2);

    t.eq(Opt.fmap(None, x -> x*2), None);
    t.eq(Opt.get(Opt.fmap(Some(4), x -> x*2)), 8);

    t.eq(Opt.bind(Some(4), x -> None), None);
    t.eq(Opt.get(Opt.bind(Some(4), x -> Some(x * 2))), 8);

    t.log();
  }
}
