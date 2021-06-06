// Copyright 15-Jun-2020 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

import dm.It;
import dm.Tp;
import dm.Dec;

/// Utilities for managing random data.
class Rnd {
  /// Returns an integer between 0 (inclusive) and n (exclusive)
  ///   n : Must be > 0, otherwise is changed to 0
  public static function i (n: Float): Int {
    if (n < 0) {
      n = 0;
    }
    return Math.floor(Math.random() * n);
  }


  /// Returns a random Float between n1 (inclusive) and n2 (inclusive) with
  /// 'd' : decimals. (n2 can be less than n1)
  ///   d  : Decimal (between [0-9])
  ///   n1 : A limit
  ///   n2 : Another limit
  public static function f (n1: Float, n2: Float, d: Int): Float {
    return Dec.round(n1 + Math.random() * (n2 - n1), d);
  };

  /// Rearranges elements of 'a' randomly.
  public static function shuffle<T> (a: Array<T>) {
    var j: Int;
    var tmp: T;
    var i = a.length;
    while (i > 1) {
      j = Math.floor(Math.random() * i--);
      tmp = a[i];
      a[i] = a[j];
      a[j] = tmp;
    }
  }

  /// Returns a Box with repeated elements
  ///   es : Description of box elements. For example:
  ///        new Box [("a", 1),("b", 2)] creates elements "a","b","b".
  public static function mkBox<T> (es: Array<Tp<T, Int>>): Box<T> {
    var r = [];
    It.from(es).each(e -> {
      It.range(0, e.e2).each(n ->  r.push(e.e1));
    });
    return new Box(r);
  };
}

/// Object for selecting among a group of elements in random way. When all
/// elements have been selected, Box is reloaded with elements in different
/// order.
class Box<T> {

  /// Elements of Box in original order
  var es(default, null): Array<T>;
  /// Current elements of Box
  var box(default, null): Array<T>;

  /// 'es' are elements of Box.
  public function new (es: Array<T>) {
    this.es = es;
    box = It.from(es).shuffle().to();
  }

  /// Returns next random element.
  public function next (): T {
    if (box.length == 0) {
      box = It.from(es).shuffle().to();
    }
    return box.pop();
  }
}

