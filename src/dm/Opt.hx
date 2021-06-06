// Copyright 15-Jun-2020 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

/// Container of a value which can be empty.
enum Option<T> {
  Some(v:T);
  None;
}

/// Option utilities.
class Opt {
  /// Returns 'o' value if 'o' is 'Some(value)'. Otherwise it returns null.
  public static function get<T> (o: Option<T>): Null<T> {
    switch (o){
      case Some(value): return value;
      default: return null;
    }
  }

  /// Returns 'o' value if 'o' is 'Some(value)'. Otherwise it returns 'v'.
  public static function oget<T> (o: Option<T>, v: T): T {
    switch (o){
      case Some(value): return value;
      default: return v;
    }
  }

  /// Returns 'o' value if 'o' is 'Some(value)'. Otherwise throws an exception.
  public static function eget<T> (o: Option<T>): T {
    switch (o){
      case Some(value): return value;
      default: throw ("Option is None");
    }
  }

  /// Returns fn(e)
  public static function fmap<T, U> (e: T, fn: T -> Option<U>): Option<U> {
    return fn(e);
  }

  /// Returns fn(vaule) if e is Some(value) or None if e is None.
  public static function bind<T, U> (
    e: Option<T>, fn: T -> Option<U>
  ): Option<U> {
    return switch e {
      case Some(value): fn(value);
      default: None;
    }
  }

}
