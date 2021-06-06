// Copyright 15-Jun-2020 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

/// Tuple of two elements.
class Tp<T, U> {

  public function new (e1: T, e2: U) {
    this.e1 = e1;
    this.e2 = e2;
  }

  public var e1(default, null): T;

  public var e2(default, null): U;

  @:op(A == B)
  public static function equals<T, U> (tp1: Tp<T, U>, tp2: Tp<T, U>): Bool {
    return tp1.e1 == tp2.e1 && tp1.e2 == tp2.e2;
  }

  @:op(A != B)
  public static function nequals<T, U> (tp1: Tp<T, U>, tp2: Tp<T, U>): Bool {
      return !(tp1 == tp2);
  }

  public function toString (): String {
    return '(${this.e1}, ${this.e2})';
  }

}
