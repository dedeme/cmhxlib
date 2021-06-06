// Copyright 15-Jun-2020 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

/// Tuple of three elements.
class Tp3<T, U, V> {

  public function new (e1: T, e2: U, e3: V) {
    this.e1 = e1;
    this.e2 = e2;
    this.e3 = e3;
  }

  public var e1(default, null): T;

  public var e2(default, null): U;

  public var e3(default, null): V;

  @:op(A == B)
  public static function equals<T, U, V> (
    tp1: Tp3<T, U, V>, tp2: Tp3<T, U, V>
  ): Bool {
    return tp1.e1 == tp2.e1 && tp1.e2 == tp2.e2 && tp1.e3 == tp2.e3;
  }

  @:op(A != B)
  public static function nequals<T, U, V> (
    tp1: Tp3<T, U, V>, tp2: Tp3<T, U, V>
  ): Bool {
      return !(tp1 == tp2);
  }

  public function toString () {
    return '(${this.e1}, ${this.e2}, ${this.e3})';
  }
}
