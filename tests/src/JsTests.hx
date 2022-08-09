// Copyright 13-Aug-2019 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

import dm.Test;
import dm.Js;
import dm.Opt;
import haxe.ds.Option;

private class Tst {
  public final s: String;
  public final i: Int;
  var i2: Int = 0;
  public function new (s:String, i:Int) {
    this.s = s;
    this.i = i;
  }
  public function setI2 (n: Int) {
    i2 = n;
  }
  public function getI2 (): Int {
    return i2;
  }
  public static function toJs (t:Tst): Js {
    return Js.wa([
      Js.ws(t.s),
      Js.wi(t.i),
      Js.wi(t.i2)
    ]);
  }
  public static function fromJs (js:Js): Tst {
    final a = js.ra();

    final s = a[0].rs();
    final i = a[1].ri();
    final i2 = a[2].ri();

    final r = new Tst(s, i);
    r.i2 = i2;
    return r;
  }
}

class JsTests {
  public static function run() {
    final t = new Test("Js");


    t.yes(Js.from(Js.wn().to()).isNull());
    t.eq(Js.from(Js.wb(true).to()).rb(), true);
    t.eq(Js.wb(true).to(), "true");
    t.eq(Js.from(Js.wb(false).to()).rb(), false);
    t.eq(Js.wb(false).to(), "false");
    t.eq(Js.from(Js.wi(12).to()).ri(), 12);
    t.eq(Js.wi(12).to(), "12");
    t.eq(Js.from(Js.wf(12.34).to()).rf(), 12.34);
    t.eq(Js.wf(12.34).to(), "12.34");
    t.eq(Js.from(Js.ws("\"Cañón\"").to()).rs(), "\"Cañón\"");
    t.eq(Js.ws("\"Cañón\"").to(), "\"\\\"Cañón\\\"\"");
    var a = Js.wa([Js.wb(true), Js.wi(3)]).ra();
    t.eq(a[0].rb(), true);
    t.eq(a[1].ri(), 3);
    t.eq(Js.wa([Js.wb(true), Js.wi(3)]).to(), "[true,3]");
    var o = Js.from(Js.wo(["a" => Js.wb(true), "b" => Js.wi(3)]).to()).ro();
    t.eq(o.get("a").rb(), true);
    t.eq(o.get("b").ri(), 3);
    var r = Js.wo(["a" => Js.wb(true), "b" => Js.wi(3)]).to();
    t.eq(r, StringTools.startsWith(r, "{\"a")
      ? "{\"a\":true,\"b\":3}"
      : "{\"b\":3,\"a\":true}"
    );

    var tst = new Tst("a", 2);
    tst.setI2(4);
    var tst2 = Tst.fromJs(Js.from(Tst.toJs(tst).to()));
    t.eq(tst.s, tst2.s);
    t.eq(tst.i, tst2.i);
    t.eq(tst.getI2(), tst2.getI2());

    var tstb = new Tst("b", 22);
    tstb.setI2(44);

    //trace(Js.wArray([tst, tstb], Tst.toJs).to());
    var a2 = Js.from(Js.wArray([tst, tstb], Tst.toJs).to()).rArray(Tst.fromJs);
    tst2 = a2[0];
    var tstb2 = a2[1];
    t.eq(tst.s, tst2.s);
    t.eq(tst.i, tst2.i);
    t.eq(tst.getI2(), tst2.getI2());
    t.eq(tstb.s, tstb2.s);
    t.eq(tstb.i, tstb2.i);
    t.eq(tstb.getI2(), tstb2.getI2());

    var m = Js.from(Js.wMap(["a" => tst, "b" => tstb], Tst.toJs).to())
      .rMap(Tst.fromJs);
    tst2 = m["a"];
    tstb2 = m["b"];
    t.eq(tst.s, tst2.s);
    t.eq(tst.i, tst2.i);
    t.eq(tst.getI2(), tst2.getI2());
    t.eq(tstb.s, tstb2.s);
    t.eq(tstb.i, tstb2.i);
    t.eq(tstb.getI2(), tstb2.getI2());

    t.log();
  }
}
