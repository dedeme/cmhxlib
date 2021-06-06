// Copyright 15-Jun-2020 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

import haxe.io.Bytes;
import dm.Cryp;

/// Static functions for string management.
class Str {
  /// Cuts [text] left, returning [width] positions at right.
  public static function cutLeft (text: String, width: Int): String {
    if (text.length > width)
      return "..." + text.substring (text.length - width + 3);
    return text;
  }

  /// Cuts [text] right, returning [width] positions at left.
  public static function cutRight (text: String, width: Int): String {
    if (text.length > width)
      return text.substring (0, width - 3) + "...";
    return text;
  }

  /// It does not escape single nor double quotes.
  inline public static function html (text: String): String {
    return StringTools.htmlEscape (text, false);
  }

  /// Indicates if text[0] is a space. if text length is 0, returns false.
  public static function isSpace (text: String): Bool {
    return (text.length == 0)? false: StringTools.isSpace (text, 0);
  }

  /// Indicates if text[0] is a letter or '_'.
  /// if text length is 0, returns false.
  public static function isLetter (text: String): Bool {
    if (text.length == 0) return false;

    var ch = text.charAt(0);
    return (ch >= "a" && ch <= "z") || (ch >= "A" && ch <= "Z" || ch == "_");
  }

  /// Indicates if text[0] is a digit. if text length is 0, returns false.
  public static function isDigit (text: String): Bool {
    if (text.length == 0) return false;

    var ch = text.charAt(0);
    return (ch >= "0" && ch <= "9");
  }

  /// Indicates if text[0] is a letter, '_' or digit.
  /// if text length is 0, returns false.
  public static function isLetterOrDigit (text: String): Bool {
    return isLetter (text) || isDigit (text);
  }

  /// Returns the index of first match of a character of [text] with
  /// whatever character of [match], or -1 if it has not match.
  /// For example: 'index("Hello World", "lzw")' returns '2'.
  public static function index (text: String, match: String): Int {
    var lg = text.length;
    var ix = 0;
    while (ix < lg) {
      if (match.indexOf(text.charAt(ix)) != -1) return ix;
      ++ix;
    }
    return -1;
  }

  /// Returns s1 < s2 ? -1: s1 > s2 ? 1: 0;
  public static function compare (s1: String, s2: String): Int {
    return s1 < s2 ? -1: s1 > s2 ? 1: 0;
  }

  /// ONLY JS - Returns s1 < s2 ? -1: s1 > s2 ? 1: 0; in locale
  public static function localeCompare (s1: String, s2: String): Int {
    #if js
    return untyped js.Syntax.code("s1.localeCompare(s2);");
    #else
    throw new haxe.Exception("Without impletation");
    #end
  }

  /// Returns one new string, that is a substring of [s].
  /// Result includes the character [begin] and excludes the
  /// character [end]. If 'begin < 0' or 'end < 0' they are converted to
  /// 's.length+begin' or 's.length+end'.
  /// Next rules are applied in turn:
  ///   If 'begin < 0' or 'end < 0' they are converted to 's.length+begin' or
  ///      's.length+end'.
  ///   If 'begin < 0' it is converted to '0'.
  ///   If 'end > s.length' it is converted to 's.length'.
  ///   If 'end <= begin' then returns a empty string.
  /// If prarameter [end] is missing, the return is equals to
  /// 'sub(s, 0, begin)'.
  /// Parameters:
  ///   s     : String for extracting a substring.
  ///   begin : Position of first character, inclusive.
  ///   end   : Position of last character, exclusive. It can be missing.
  ///   return: A substring of [s]
  public static function sub (s: String, begin: Int, ?end: Int): String {
    if (end == null) end = s.length;
    var lg = s.length;
    if (begin < 0) begin += lg;
    if (end < 0) end += lg;
    if (begin < 0) begin = 0;
    if (end > lg) end = lg;
    if (end <= begin) return "";
    return s.substring (begin, end);
  }

  /// Equals to 'sub(s, 0, ix)'
  public static function left (s: String, ix: Int): String {
    return sub(s, 0, ix);
  }

  /// Equals to 'sub(s, ix)'
  public static function right (s: String, ix: Int): String {
    return sub(s, ix);
  }

  /// Returns 's' repeated 'times' times
  public static function repeat (s: String, times: Int):String {
    var bf = new StringBuf();
    for (n in 0 ... times) {
      bf.add(s);
    }
    return bf.toString();
  }

  /// ONLY JS - Javascript encodeURIComponent
  public static function encodeURIComponent (s: String): String {
    #if js
    return untyped js.Syntax.code("encodeURIComponent(s)");
    #else
    throw new haxe.Exception("Without impletation");
    #end
  }

  /// ONLY JS - Javascript decodeURIComponent
  public static function decodeURIComponent (url: String): String {
    #if js
    return untyped js.Syntax.code("decodeURIComponent(url)");
    #else
    throw new haxe.Exception("Without impletation");
    #end
  }

  /// ONLY JS - Javascript encodeURI
  public static function encodeURI (s: String): String {
    #if js
    return untyped js.Syntax.code("encodeURI(s)");
    #else
    throw new haxe.Exception("Without impletation");
    #end
  }

  /// ONLY JS - Javascript decodeURI
  public static function decodeURI (url: String): String {
    #if js
    return untyped js.Syntax.code("decodeURI(url)");
    #else
    throw new haxe.Exception("Without impletation");
    #end
  }

}

