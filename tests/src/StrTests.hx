// Copyright 16-Jun-2020 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

import dm.Test;
import dm.Cryp;
import dm.Str;
import dm.Tp;
import dm.It;

class StrTests {
  public static function run () {
    var t = new Test("Str");

    t.eq(StringTools.trim("  "), "");
    t.eq(StringTools.trim(" a"), "a");
    t.eq(StringTools.trim("a   "), "a");
    t.eq(StringTools.trim("\na\t\t"), "a");
    t.eq(StringTools.trim(" \na n c\t\t "), "a n c");

    t.eq("", StringTools.trim(" \n\t "));
    t.eq("", StringTools.ltrim(" \n\t "));
    t.eq("", StringTools.rtrim(" \n\t "));

    t.eq("abc", StringTools.trim(" \nabc\t "));
    t.eq("abc\t ", StringTools.ltrim(" \nabc\t "));
    t.eq(" \nabc", StringTools.rtrim(" \nabc\t "));

    t.yes(StringTools.startsWith("", ""));
    t.yes(StringTools.startsWith("abc", ""));
    t.yes(!StringTools.startsWith("", "abc"));
    t.yes(StringTools.startsWith("abc", "a"));
    t.yes(StringTools.startsWith("abc", "abc"));
    t.yes(!StringTools.startsWith("abc", "b"));

    t.yes(StringTools.endsWith("", ""));
    t.yes(StringTools.endsWith("abc", ""));
    t.yes(!StringTools.endsWith("", "abc"));
    t.yes(StringTools.endsWith("abc", "c"));
    t.yes(StringTools.endsWith("abc", "abc"));
    t.yes(!StringTools.endsWith("abc", "b"));

    var arr = ["pérez", "pera", "p zarra", "pizarra"];
    var arr2 = It.from(arr).sort(Str.compare).to();
    t.eq(["p zarra", "pera", "pizarra", "pérez"].toString(), arr2.toString());
    arr2 = It.from(arr).sort(Str.localeCompare).to();
    t.eq(["p zarra", "pera", "pérez", "pizarra"].toString(), arr2.toString());

    t.eq(Str.cutLeft ("", 3), "");
    t.eq(Str.cutLeft ("ab", 3), "ab");
    t.eq(Str.cutLeft ("abcde", 4), "...e");
    t.eq(Str.cutLeft ("abcd", 3), "...");
    t.eq(Str.cutLeft ("abcd", 1), "...");

    t.eq(Str.cutRight ("", 3), "");
    t.eq(Str.cutRight ("ab", 3), "ab");
    t.eq(Str.cutRight ("abcde", 4), "a...");
    t.eq(Str.cutRight ("abcd", 3), "...");
    t.eq(Str.cutRight ("abcd", 1), "...");

    t.eq(Str.html ("a'bc<"), "a'bc&lt;");

    t.yes(!Str.isSpace (""));
    t.yes(Str.isSpace (" "));
    t.yes(!Str.isSpace ("v"));
    t.yes(!Str.isSpace ("_"));
    t.yes(!Str.isSpace ("2"));
    t.yes(!Str.isSpace ("."));
    t.yes(!Str.isSpace ("v-"));
    t.yes(!Str.isSpace ("_-"));
    t.yes(!Str.isSpace ("2-"));
    t.yes(!Str.isSpace (".-"));

    t.yes(!Str.isLetter (""));
    t.yes(!Str.isLetter (" "));
    t.yes(Str.isLetter ("v"));
    t.yes(Str.isLetter ("_"));
    t.yes(!Str.isLetter ("2"));
    t.yes(!Str.isLetter ("."));
    t.yes(Str.isLetter ("v-"));
    t.yes(Str.isLetter ("_-"));
    t.yes(!Str.isLetter ("2-"));
    t.yes(!Str.isLetter (".-"));

    t.yes(!Str.isDigit (""));
    t.yes(!Str.isDigit (" "));
    t.yes(!Str.isDigit ("v"));
    t.yes(!Str.isDigit ("_"));
    t.yes(Str.isDigit ("2"));
    t.yes(!Str.isDigit ("."));
    t.yes(!Str.isDigit ("v-"));
    t.yes(!Str.isDigit ("_-"));
    t.yes(Str.isDigit ("2-"));
    t.yes(!Str.isDigit (".-"));

    t.yes(!Str.isLetterOrDigit (""));
    t.yes(!Str.isLetterOrDigit (" "));
    t.yes(Str.isLetterOrDigit ("v"));
    t.yes(Str.isLetterOrDigit ("_"));
    t.yes(Str.isLetterOrDigit ("2"));
    t.yes(!Str.isLetterOrDigit ("."));
    t.yes(Str.isLetterOrDigit ("v-"));
    t.yes(Str.isLetterOrDigit ("_-"));
    t.yes(Str.isLetterOrDigit ("2-"));
    t.yes(!Str.isLetterOrDigit (".-"));

    t.eq(Str.sub("", -100), "");
    t.eq(Str.sub("", -2), "");
    t.eq(Str.sub("", 0), "");
    t.eq(Str.sub("", 2), "");
    t.eq(Str.sub("", 100), "");
    t.eq(Str.sub("a", -100), "a");
    t.eq(Str.sub("a", -2), "a");
    t.eq(Str.sub("a", 0), "a");
    t.eq(Str.sub("a", 2), "");
    t.eq(Str.sub("a", 100), "");
    t.eq(Str.sub("12345", -100), "12345");
    t.eq(Str.sub("12345", -2), "45");
    t.eq(Str.sub("12345", 0), "12345");
    t.eq(Str.sub("12345", 2), "345");
    t.eq(Str.sub("12345", 100), "");

    t.eq(Str.sub("", -100, -100), "");
    t.eq(Str.sub("", -2, -100), "");
    t.eq(Str.sub("", 0, -100), "");
    t.eq(Str.sub("", 2, -100), "");
    t.eq(Str.sub("", 100, -100), "");

    t.eq(Str.sub("", -100, -2), "");
    t.eq(Str.sub("", -2, -2), "");
    t.eq(Str.sub("", 0, -2), "");
    t.eq(Str.sub("", 2, -2), "");
    t.eq(Str.sub("", 100, -2), "");

    t.eq(Str.sub("", -100, 0), "");
    t.eq(Str.sub("", -2, 0), "");
    t.eq(Str.sub("", 0, 0), "");
    t.eq(Str.sub("", 2, 0), "");
    t.eq(Str.sub("", 100, 0), "");

    t.eq(Str.sub("", -100, 2), "");
    t.eq(Str.sub("", -2, 2), "");
    t.eq(Str.sub("", 0, 2), "");
    t.eq(Str.sub("", 2, 2), "");
    t.eq(Str.sub("", 100,2), "");

    t.eq(Str.sub("", -100, 100), "");
    t.eq(Str.sub("", -2, 100), "");
    t.eq(Str.sub("", 0, 100), "");
    t.eq(Str.sub("", 2, 100), "");
    t.eq(Str.sub("", 100, 100), "");

    t.eq(Str.sub("a", -100, -100), "");
    t.eq(Str.sub("a", -2, -100), "");
    t.eq(Str.sub("a", 0, -100), "");
    t.eq(Str.sub("a", 2, -100), "");
    t.eq(Str.sub("a", 100, -100), "");

    t.eq(Str.sub("a", -100, -2), "");
    t.eq(Str.sub("a", -2, -2), "");
    t.eq(Str.sub("a", 0, -2), "");
    t.eq(Str.sub("a", 2, -2), "");
    t.eq(Str.sub("a", 100, -2), "");

    t.eq(Str.sub("a", -100, 0), "");
    t.eq(Str.sub("a", -2, 0), "");
    t.eq(Str.sub("a", 0, 0), "");
    t.eq(Str.sub("a", 2, 0), "");
    t.eq(Str.sub("a", 100, 0), "");

    t.eq(Str.sub("a", -100, 2), "a");
    t.eq(Str.sub("a", -2, 2), "a");
    t.eq(Str.sub("a", 0, 2), "a");
    t.eq(Str.sub("a", 2, 2), "");
    t.eq(Str.sub("a", 100,2), "");

    t.eq(Str.sub("a", -100, 100), "a");
    t.eq(Str.sub("a", -2, 100), "a");
    t.eq(Str.sub("a", 0, 100), "a");
    t.eq(Str.sub("a", 2, 100), "");
    t.eq(Str.sub("a", 100, 100), "");

    t.eq(Str.sub("12345", -100, -100), "");
    t.eq(Str.sub("12345", -2, -100), "");
    t.eq(Str.sub("12345", 0, -100), "");
    t.eq(Str.sub("12345", 2, -100), "");
    t.eq(Str.sub("12345", 100, -100), "");

    t.eq(Str.sub("12345", -100, -2), "123");
    t.eq(Str.sub("12345", -2, -2), "");
    t.eq(Str.sub("12345", 0, -2), "123");
    t.eq(Str.sub("12345", 2, -2), "3");
    t.eq(Str.sub("12345", 100, -2), "");

    t.eq(Str.sub("12345", -100, 0), "");
    t.eq(Str.sub("12345", -2, 0), "");
    t.eq(Str.sub("12345", 0, 0), "");
    t.eq(Str.sub("12345", 2, 0), "");
    t.eq(Str.sub("12345", 100, 0), "");

    t.eq(Str.sub("12345", -100, 2), "12");
    t.eq(Str.sub("12345", -2, 2), "");
    t.eq(Str.sub("12345", 0, 2), "12");
    t.eq(Str.sub("12345", 2, 2), "");
    t.eq(Str.sub("12345", 100,2), "");

    t.eq(Str.sub("12345", -100, 100), "12345");
    t.eq(Str.sub("12345", -2, 100), "45");
    t.eq(Str.sub("12345", 0, 100), "12345");
    t.eq(Str.sub("12345", 2, 100), "345");
    t.eq(Str.sub("12345", 100, 100), "");

    t.eq(Str.left("", 2), "");
    t.eq(Str.left("12345", 2), "12");
    t.eq(Str.left("12345", -2), "123");

    t.eq(Str.right("", 2), "");
    t.eq(Str.right("12345", 2), "345");
    t.eq(Str.right("12345", -2), "45");

    t.eq(
      Str.decodeURIComponent(Str.encodeURIComponent(
        "http://www.es.dr/\"abv\"_()<")),
      "http://www.es.dr/\"abv\"_()<"
    );

    t.eq(
      Str.decodeURI(Str.encodeURI(
        "http://www.es.dr/\"abv\"_()<")),
      "http://www.es.dr/\"abv\"_()<"
    );

    t.log();

  }
}
