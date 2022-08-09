// Copyright 15-Aug-2019 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

import dm.Test;
import dm.Exc;

class ExcTests {

  public static function run() {
    final t = new Test("Exc");

    try {
      throw Exc.illegalState("Message");
    } catch (e:String) {
      //trace(e);
      t.eq(Exc.type(e), EIllegalState);
    }

    try {
      throw Exc.range(0, 7, 9);
    } catch (e:String) {
      //trace(e);
      t.eq(Exc.type(e), ERange);
    }

    try {
      throw Exc.illegalArgument("var", 5, 1234);
    } catch (e:String) {
      //trace(e);
      t.eq(Exc.type(e), EIllegalArgument);
    }

    try {
      throw Exc.io("File not found");
    } catch (e:String) {
      //trace(e);
      t.eq(Exc.type(e), EIo);
    }

    t.log();
  }

}
