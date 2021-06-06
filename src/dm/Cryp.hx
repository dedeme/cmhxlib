// Copyright 15-Jun-2020 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

import haxe.io.Bytes;

/// Utilities for encryption.
class Cryp {

  /// Generates a B64 random key of a length 'lg'.
  ///   lg    : Key length
  ///   return: Random key
  public static function genK (lg: Int): String {
    var bs = Bytes.alloc(lg);
    for (i in 0...lg) {
      bs.set(i, Std.random(256));
    }
    return B64.encodeBytes(bs).substring(0, lg);
  }

  /// Returns 'k' codified in irreversible way, using 'lg' B64 digits.
  ///   key   : String to codify
  ///   lg    : Length of result
  ///   return: 'lg' B64 digits
  public static function key (key: String, lg: Int): String {
    var k = B64.decodeBytes(B64.encode(
      key + "codified in irreversibleDeme is good, very good!\n\r8@@"
    ));
    final lenk = k.length;
    var sum = 0;
    for (i in 0...lenk)
      sum += k.get(i);

    final lg2 = lg + lenk;
    final r = Bytes.alloc(lg2);
    final r1 = Bytes.alloc(lg2);
    final r2 = Bytes.alloc(lg2);
    var ik = 0;
    for (i in 0...lg2) {
      final v1 = k.get(ik);
      final v2 = v1 + k.get(v1 % lenk);
      final v3 = v2 + k.get(v2 % lenk);
      final v4 = v3 + k.get(v3 % lenk);
      sum = (sum + i + v4) % 256;
      r1.set(i, sum);
      r2.set(i, sum);
      ++ik;
      if (ik == lenk)
        ik = 0;
    }

    for (i in 0...lg2) {
      final v1 = r2.get(i);
      final v2 = v1 + r2.get(v1 % lg2);
      final v3 = v2 + r2.get(v2 % lg2);
      final v4 = v3 + r2.get(v3 % lg2);
      sum = (sum + v4) % 256;
      r2.set(i, sum);
      r.set(i, (sum + r1.get(i)) % 256);
    }

    return B64.encodeBytes(r).substring(0, lg);
  }

  /// Encodes 'm' with key 'k'.
  ///   key   : Key for encoding
  ///   msg   : Message to encode
  ///   return: 'm' codified in B64 digits.
  public static function cryp (key: String, msg: String): String {
    final m = B64.encode(msg);
    final lg = m.length;
    final k = Cryp.key(key, lg);
    final r = Bytes.alloc(lg);
    for (i in 0...lg)
      r.set(i, m.charCodeAt(i) + k.charCodeAt(i));

    return B64.encodeBytes(r);
  }

  /// Decodes 'c' using key 'k'. 'c' was codified with cryp().
  ///   key   : Key for decoding
  ///   c     : Text codified with cryp()
  ///   return: 'c' decoded.
  public static function decryp (key: String, c: String): String {
    final bs = B64.decodeBytes(c);
    final lg = bs.length;
    final k = Cryp.key(key, lg);
    final r = new StringBuf();
    for (i in 0...lg) {
      r.add(String.fromCharCode(bs.get(i) - k.charCodeAt(i)));
    }

    return B64.decode(r.toString());
  }

}
