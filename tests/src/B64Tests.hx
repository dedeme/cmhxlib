// Copyright 09-Aug-2019 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

import dm.Test;
import dm.B64;
import haxe.io.UInt8Array;

class B64Tests {
  public static function run() {
    final t = new Test("B64");

    t.eq(B64.encode("Cañónç䍆"), "Q2HDscOzbsOn5I2G");
    t.eq(B64.decode(B64.encode("Cañónç䍆")), "Cañónç䍆");
    var bs = UInt8Array.fromArray([34, 12, 27, 1]).get_view().buffer;
    var bs2 = B64.decodeBytes(B64.encodeBytes(bs));
    for (i in 0...4)
      t.eq(bs.get(i), bs2.get(i));

    t.log();
  }
}
