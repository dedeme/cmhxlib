// Copyright 09-Aug-2022 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

/// Container of a computation which can produce an error.
enum Result<T> {
  Ok (v: T);
  Error (s: String);
}

/// Result utilities.
class Rs {
  /// Returns Ok(fn(value)) if 'e' is Ok(value) or Error(x) if 'e' is Error(x).
  public static function fmap<T, U> (e: Result<T>, fn: T -> U): Result<U> {
    return switch (e) {
      case Ok(value): Ok(fn(value));
      case Error(s): Error(s);
    }
  }

  /// Returns
  ///   - Ok(v2) if 'e' is Ok(v1) and fn(v1) returns Ok(v2)
  ///   - Error(e) if 'e' is Ok(v) and fn(v) returns Error(e)
  ///   - Error(e) if 'e' is Error(e).
  public static function bind<T, U> (
    e: Result<T>, fn: T -> Result<U>
  ): Result<U> {
    return switch (e) {
      case Ok(value): fn(value);
      case Error(s): Error(s);
    }
  }
}
