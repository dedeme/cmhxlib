// Copyright 09-Aug-2019 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

import dm.Test;
import dm.It;
import dm.Opt;
import dm.Tp;
import dm.Tp3;

class ItTests {

  public static function run() {
    final t = new Test("It");

    t.not(It.empty().hasNext());
    t.eq(It.empty().count(), 0);

    var a = [];
    t.not(It.from(a).hasNext());
    t.yes(It.empty().eq(It.from(a)));
    t.eq(It.from(a).count(), 0);
    t.eq(It.from(a).toString(), "It[]");
    t.eq(It.from(a).cat(It.from(a)).toString(), "It[]");
    t.eq(It.from(a).push("A").toString(), "It[A]");
    t.eq(It.from(a).unshift("A").toString(), "It[A]");
    t.not(It.from(a).contains(""));
    t.eq(It.from(a).index(""), -1);
    t.eq(It.from(a).indexf(e -> e == ""), -1);
    t.eq(It.from(a).lastIndex(""), -1);
    t.eq(It.from(a).lastIndexf(e -> e == ""), -1);
    t.yes(It.from(a).every(e -> e == "a"));
    t.not(It.from(a).some(e -> e == "a"));
    t.eq(Opt.get(It.from(a).find(e -> e == "a")), null);
    t.eq(Opt.get(It.from(a).findLast(e -> e == "a")), null);
    t.eq(It.from(a).filter(e -> e == "a").count(), 0);
    t.yes(It.from(a).reverse().eq(It.from(a)));
    t.yes(It.from(a).take(2).eq(It.from(a)));
    t.yes(It.from(a).drop(2).eq(It.from(a)));
    t.yes(It.from(a).shuffle().eq(It.from(a)));
    t.yes(It.from(a).map(e -> e, e -> ', $e').eq(It.empty()));
    t.yes(It.split("", "").eq(It.from(a)));
    t.yes(It.split("", "2").eq(It.from([""])));
    t.eq(It.join(It.split("", ""), ""), "");
    t.eq(It.join(It.split("", "2"), "2"), "");

    a = ["zzz"];
    t.eq(It.unary("zzz").toString(), "It[zzz]");
    t.not(It.unary("zza") == It.from(a));
    t.yes(It.unary("zza").eq(
      It.from(a),
      (e1, e2) -> e1.charAt(3) == e2.charAt(3)
    ));
    t.eq(It.from(a).count(), 1);
    t.eq(It.from(a).toString(), "It[zzz]");
    t.eq(It.from(a).cat(It.empty()).toString(), "It[zzz]");
    t.eq(It.empty().cat(It.from(a)).toString(), "It[zzz]");
    t.yes(It.from(a).contains("zzz"));
    t.not(It.from(a).contains("zza"));
    t.yes(It.from(a).contains(
      "zza",
      (e1, e2) -> e1.charAt(3) == e2.charAt(3)
    ));
    t.eq(It.from(a).index("zzz"), 0);
    t.eq(It.from(a).index("zza"), -1);
    t.eq(It.from(a).index(
      "zza",
      (e1, e2) -> e1.charAt(1) == e2.charAt(1)
    ), 0);
    t.eq(It.from(a).indexf(e -> e == "zzz"), 0);
    t.eq(It.from(a).indexf(e -> e == "zza"), -1);
    t.eq(It.from(a).indexf(e -> e.charAt(2) == "z"), 0);
    t.eq(It.from(a).lastIndex("zzz"), 0);
    t.eq(It.from(a).lastIndex("zza"), -1);
    t.eq(It.from(a).lastIndex(
      "zza",
      (e1, e2) -> e1.charAt(1) == e2.charAt(1)
    ), 0);
    t.eq(It.from(a).lastIndexf(e -> e == "zzz"), 0);
    t.eq(It.from(a).lastIndexf(e -> e == "zza"), -1);
    t.eq(It.from(a).lastIndexf(e -> e.charAt(2) == "z"), 0);
    t.yes(It.from(a).every(e -> e == "zzz"));
    t.yes(It.from(a).some(e -> e == "zzz"));
    t.not(It.from(a).every(e -> e == "a"));
    t.not(It.from(a).some(e -> e == "a"));
    t.eq(Opt.get(It.from(a).find(e -> e == "a")), null);
    t.eq(Opt.get(It.from(a).findLast(e -> e == "a")), null);
    t.eq(It.from(a).filter(e -> e == "a").count(), 0);
    t.eq(Opt.get(It.from(a).find(e -> e == "zzz")), "zzz");
    t.eq(Opt.get(It.from(a).findLast(e -> e == "zzz")), "zzz");
    t.eq(It.from(a).filter(e -> e == "zzz").count(), 1);
    t.yes(It.from(a).reverse().eq(It.from(a)));
    t.yes(It.from(a).take(2).eq(It.from(a)));
    t.yes(It.from(a).drop(2).eq(It.empty()));
    t.yes(It.from(a).shuffle().eq(It.from(a)));
    t.yes(It.from(a).map(e -> e, e -> ', $e').eq(It.from(a)));
    t.yes(It.split("zzz", "").eq(It.from(["z","z","z"])));
    t.yes(It.split("zzz", "2").eq(It.from(a)));
    t.eq(It.join(It.split("zzz", ""), ""), "zzz");
    t.eq(It.join(It.split("zzz", "2"), "2"), "zzz");

    a = ["a", "b", "c"];
    t.eq(It.from(a).count(), 3);
    t.eq(It.from(a).toString(), "It[a,b,c]");
    t.eq(It.from(a).cat(It.unary("z")).toString(), "It[a,b,c,z]");
    t.eq(It.unary("z").cat(It.from(a)).toString(), "It[z,a,b,c]");
    t.not(It.from(a).every(e -> e == "zzz"));
    t.not(It.from(a).some(e -> e == "zzz"));
    t.not(It.from(a).every(e -> e == "a"));
    t.yes(It.from(a).some(e -> e == "a"));
    t.yes(It.from(a).every(e -> e != "zzz"));
    t.yes(It.from(a).some(e -> e != "zzz"));
    t.eq(It.from(a).reverse().toString(), "It[c,b,a]");
    t.eq(It.from(a).take(2).toString(), "It[a,b]");
    t.eq(It.from(a).drop(2).toString(), "It[c]");
    t.eq(It.from(a).shuffle().count(), 3);
    //trace(It.from(a).shuffle().toString());
    //trace(It.from(a).shuffle().toString());
    t.yes(It.from(a).map(e -> e, e -> ', $e').eq(It.from(["a", ", b", ", c"])));
    t.yes(It.split("abc", "").eq(It.from(a)));
    t.yes(It.split("abc", "b").eq(It.from(["a","c"])));
    t.yes(It.split("abc", "c").eq(It.from(["ab",""])));
    t.eq(It.join(It.split("abc", "b"), "b"), "abc");
    t.eq(It.join(It.split("abc", "c"), "c"), "abc");

    var is: Array<Int> = [];
    t.not(It.from(is).hasNext());
    t.yes(It.from(is).eq(It.empty()));
    t.eq(It.from(is).count(), 0);
    t.eq(It.from(is).toString(), "It[]");
    t.eq(It.from(is).cat(It.from(is)).toString(), "It[]");
    t.eq(It.from(is).push(1).toString(), "It[1]");
    t.eq(It.from(is).unshift(1).toString(), "It[1]");
    var sum = 0;
    It.from(is).each(n -> sum += n);
    t.eq(sum, 0);
    var sumTx = "";
    It.from(is).eachSyn(
      (n:Int, frec:()->Void) ->
        haxe.Timer.delay(() -> {
          sumTx += "" + n;
          frec();  //NOTE: frec must be called at the end of callback.
        }, 100),
      () -> t.eq(sumTx, ""),
      (e) -> t.yes(false)
    );
    t.eq(It.from(is).reduce(0, (seed, n) -> return seed + n), 0);
    t.yes(It.from(is).takeWhile(n -> return n < 3).eq(It.from(is)));
    t.yes(It.from(is).takeUntil(n -> return n > 2).eq(It.from(is)));
    t.yes(It.from(is).dropWhile(n -> return n < 3).eq(It.from(is)));
    t.yes(It.from(is).dropUntil(n -> return n > 2).eq(It.from(is)));
    t.yes(It.from(is).map(n -> n * 2).eq(It.from(is)));

    is = [3632];
    t.yes(It.unary(3632).eq(It.from(is)));
    t.eq(It.from(is).count(), 1);
    t.eq(It.from(is).toString(), "It[3632]");
    t.eq(It.from(is).cat(It.empty()).toString(), "It[3632]");
    t.eq(It.empty().cat(It.from(is)).toString(), "It[3632]");
    t.eq(It.from(is).push(1).toString(), "It[3632,1]");
    t.eq(It.from(is).unshift(1).toString(), "It[1,3632]");
    sum = 0;
    It.from(is).each(n -> sum += n);
    t.eq(sum, 3632);
    var sumTx1 = "";
    It.from(is).eachSyn(
      (n:Int, frec:()->Void) ->
        haxe.Timer.delay(() -> {
          sumTx1 += "" + n;
          frec();  //NOTE: frec must be called at the end of callback.
        }, 100),
      () -> t.eq(sumTx1, "3632"),
      (e) -> trace(e)
    );
    t.eq(It.from(is).reduce(0, (seed, n) -> return seed + n), 3632);
    t.yes(It.from(is).takeWhile(n -> return n < 3).eq(It.empty()));
    t.yes(It.from(is).takeUntil(n -> return n > 2).eq(It.empty()));
    t.yes(It.from(is).dropWhile(n -> return n < 3).eq(It.from(is)));
    t.yes(It.from(is).dropUntil(n -> return n > 2).eq(It.from(is)));
    t.yes(It.from(is).map(n -> n * 2).eq(It.from([7264])));

    is = [1, 2, 3];
    var is2 = It.from(is).cat(It.from(is)).to(); // It[1,2,3,1,2,3]
    t.eq(It.from(is).count(), 3);
    t.eq(It.from(is).toString(), "It[1,2,3]");
    t.eq(It.from(is).cat(It.from(is)).toString(), "It[1,2,3,1,2,3]");
    sum = 0;
    It.from(is).each(n -> sum += n);
    t.eq(sum, 6);
    var sumTx2 = "";
    It.from(is).eachSyn(
      (n:Int, frec:()->Void) ->
        haxe.Timer.delay(() -> {
          sumTx2 += "" + n;
          frec();  //NOTE: frec must be called at the end of callback.
        }, 100),
      () -> t.eq(sumTx2, "123"),
      (e) -> trace(e)
    );
    t.eq(It.from(is).reduce(0, (seed, n) -> return seed + n), 6);
    t.yes(It.from(is).map(n -> n * 2).eq(It.from([2,4,6])));

    t.yes(It.from(is).contains(1));
    t.not(It.from(is).contains(4));
    t.yes(It.from(is).contains(4, (e1, e2) -> e1 % 2 == e2 % 2));
    t.eq(It.from(is2).index(1), 0);
    t.eq(It.from(is2).index(4), -1);
    t.eq(It.from(is2).index(4, (e1, e2) -> e1 % 2 == e2 % 2), 1);
    t.eq(It.from(is2).indexf(e -> e == 1), 0);
    t.eq(It.from(is2).indexf(e -> e == 4), -1);
    t.eq(It.from(is2).indexf(e -> e % 2 == 0), 1);
    t.eq(It.from(is2).lastIndex(1), 3);
    t.eq(It.from(is2).lastIndex(4), -1);
    t.eq(It.from(is2).lastIndex(4, (e1, e2) -> e1 % 2 == e2 % 2), 4);
    t.eq(It.from(is2).lastIndexf(e -> e == 1), 3);
    t.eq(It.from(is2).lastIndexf(e -> e == 4), -1);
    t.eq(It.from(is2).lastIndexf(e -> e % 2 == 0), 4);
    t.eq(Opt.get(It.from(is2).find(e -> e == 0)), null);
    t.eq(Opt.get(It.from(is2).findLast(e -> e == 0)), null);
    t.eq(It.from(is2).filter(e -> e == 0).count(), 0);
    t.eq(Opt.get(It.from(is2).find(e -> e % 2 == 1)), 1);
    t.eq(Opt.get(It.from(is2).findLast(e -> e % 2 == 1)), 3);
    t.eq(It.from(is2).filter(e -> e % 2 == 1).count(), 4);
    t.yes(It.from(is).takeWhile(n -> return n < 3).eq(It.from([1, 2])));
    t.yes(It.from(is).takeUntil(n -> return n > 2).eq(It.from([1, 2])));
    t.yes(It.from(is).dropWhile(n -> return n < 3).eq(It.from([3])));
    t.yes(It.from(is).dropUntil(n -> return n > 2).eq(It.from([3])));

    t.yes(It.range(0).eq(It.empty()));
    t.yes(It.range(4, 4).eq(It.empty()));
    t.yes(It.range(-4, -5).eq(It.empty()));
    t.yes(It.range(3).eq(It.from([0,1,2])));
    t.yes(It.range(4, 6).eq(It.from([4, 5])));
    t.yes(It.range(-5, -3).eq(It.from([-5,-4])));

    t.yes(It.box([]).eq(It.empty()));
    t.eq(It.box([3]).take(2).toString(), "It[3,3]");
    t.eq(It.mbox(["a" => 2]).take(2).toString(), "It[a,a]");
    var box = It.box([3, 4]).take(2).to();
    t.yes(
      It.from(box).eq(It.from([3,4])) ||
      It.from(box).eq(It.from([4, 3]))
    );
    var bx = It.mbox(["a" => 2, "b" => 1]).take(4).to();
    //trace(bx.toString());
    t.yes(
      It.from(bx).eq(It.from(["a","a","b","a"])) ||
      It.from(bx).eq(It.from(["a","a","b","b"])) ||
      It.from(bx).eq(It.from(["a","b","a","a"])) ||
      It.from(bx).eq(It.from(["a","b","a","b"])) ||
      It.from(bx).eq(It.from(["b","a","a","a"])) ||
      It.from(bx).eq(It.from(["b","a","a","b"]))
    );

    t.yes(It.zip(It.from([]), It.from([2])).eq(It.empty()));
    var tpa = It.zip(It.from(["a"]), It.from([2])).to();
    t.eq(tpa.length, 1);
    t.eq(tpa[0], new Tp("a", 2), Tp.equals);
    tpa = It.zip(It.from(["a", "b"]), It.from([2])).to();
    t.eq(tpa.length, 1);
    t.eq(tpa[0], new Tp("a", 2), Tp.equals);
    tpa = It.zip(It.from(["a"]), It.from([2, 6])).to();
    t.eq(tpa.length, 1);
    t.eq(tpa[0], new Tp("a", 2), Tp.equals);

    t.yes(It.zip3(It.from([]), It.from([2]), It.from([3, 4])).eq(It.empty()));
    var tpa3 = It.zip3(It.from(["a"]), It.from([2]), It.from([3])).to();
    t.eq(tpa3.length, 1);
    t.eq(tpa3[0], new Tp3("a", 2, 3), Tp3.equals);
    tpa3 = It.zip3(It.from(["a", "b", "c"]), It.from([2]), It.from([3])).to();
    t.eq(tpa3.length, 1);
    t.eq(tpa3[0], new Tp3("a", 2, 3), Tp3.equals);
    tpa3 = It.zip3(It.from(["a"]), It.from([2, 7]), It.from([3])).to();
    t.eq(tpa3.length, 1);
    t.eq(tpa3[0], new Tp3("a", 2, 3), Tp3.equals);
    tpa3 = It.zip3(It.from(["a"]), It.from([2]), It.from([3, 20, 12])).to();
    t.eq(tpa3.length, 1);
    t.eq(tpa3[0], new Tp3("a", 2, 3), Tp3.equals);

    final m1 = ["a" => 1, "b" => 2];
    final m2 = Opt.get(It.fromMap(m1).toMap());
    t.eq(m2["a"], 1);
    t.eq(m2["b"], 2);

    t.log();
  }
}
