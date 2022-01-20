// Copyright 15-Jun-2020 ºDeme
// GNU General Public License - V3 <http://www.gnu.org/licenses/>

package dm;

import dm.Opt;
import haxe.ds.StringMap;

/// Lazy iterator.
class It<T> {

  /// Returns `false` if the iteration is complete, `true` otherwise.
  /// Usually iteration is considered to be complete if all elements of the
  /// underlying data structure were handled through calls to `next()`. However,
  /// in custom iterators any logic may be used to determine the completion
  /// state.
  public final hasNext: () -> Bool;

  /// Returns the current item of the `Iterator` and advances to the next one.
  /// This method is not required to check `hasNext()` first. A call to this
  /// method while `hasNext()` is `false` yields unspecified behavior.
  /// On the other hand, iterators should not require a call to `hasNext()`
  /// before the first call to `next()` if an element is available.
  public final next: () -> T;

  // Constructors and statics --------------------------------------------------

  public function new (hasNext: () -> Bool, next: () -> T) {
    this.hasNext = hasNext;
    this.next = next;
  }

  /// Creates an It from an Iterable.
  public static function from<T> (i: Iterable<T>): It<T> {
    var it = i.iterator();
    return new It(it.hasNext, it.next);
  }

  /// Creates an It over characters of 's'.
  public static function fromString (s: String): It<String> {
    final len = s.length;
    var ix = 0;
    return new It(
      () -> ix < len,
      () -> s.charAt(ix++)
    );
  }

  /// Creates an It over keys-values of 'm'.
  public static function fromMap <V>(m: Map<String, V>): It<Tp<String, V>> {
    final kvs = m.keyValueIterator();
    return new It(
      () -> kvs.hasNext(),
      () -> {
        final kv = kvs.next();
        new Tp(kv.key, kv.value);
      }
    );
  }

  /// Creates an empty It.
  public static function empty<T> (): It<T> {
    return new It<T>(
      () -> false,
      () -> null
    );
  }

  /// Creates an It with only one element.
  public static function unary<T> (e: T): It<T> {
    return It.from([e]);
  }

  /// Returns an iterator over numbers from begin (inclusive) to end
  /// (exclusive).
  /// If 'end' is not indicated then the range is from 0 to 'begin'.
  public static function range (begin: Int, ?end: Int): It<Int> {
    if (end == null) {
      end = begin;
      begin = 0;
    }
    var c = begin;
    return new It(
      () -> c < end,
      () -> c++
    );
  }

  /// Returns an infinite random iterator over elements of 'arr'.
  public static function box<T> (arr: Array<T>) {
    final len = arr.length;
    if (len == 0)
      return It.empty();

    final a = arr.copy();
    Rnd.shuffle(a);
    var c = 0;
    return new It(
      () -> true,
      () ->
        if (c < len)
          a[c++];
        else {
          Rnd.shuffle(a);
          c = 0;
          a[c++];
        }
    );
  }

  /// Returns an infinite random iterator over elements of an array whose
  /// elements are 'm' keys repeated 'it value' times.
  /// For example:
  ///   It.mbox(["a" => 2, "b" => 1])
  /// iterates over ["a", "a", "b"]
  public static function mbox<T> (m: Map<T, Int>): It<T> {
    var a = [];
    for (k in m.keys()) {
      for (i in 0...m[k])
        a.push(k);
    }
    return box(a);
  }

  /// Returns a new It over sequencial tuples of values from 'it1' and 'it2'.
  /// The size of return is the less of 'it1' and 'it2'.
  public static function zip<T, U> (it1: It<T>, it2: It<U>): It<Tp<T, U>> {
    return new It(
      () -> it1.hasNext() && it2.hasNext(),
      () -> new Tp(it1.next(), it2.next())
    );
  }

  /// Returns a new It over sequencial tuples of values from 'it1', 'it2'
  /// and it3.
  /// The size of return is the less of 'it1', 'it2' and 'it3'.
  public static function zip3<T, U, Z> (
    it1: It<T>, it2: It<U>, it3: It<Z>
  ): It<Tp3<T, U, Z>> {
    return new It(
      () -> it1.hasNext() && it2.hasNext() && it3.hasNext(),
      () -> new Tp3(it1.next(), it2.next(), it3.next())
    );
  }

  /// Returns a new string concatenating elements of 'it' with 'sep'.
  ///   join(It.empty(), "") returns "".
  ///   join(It.empty(), "x") returns "".
  public static function join (it: It<String>, sep: String): String {
    return it.map(e -> e, e -> sep + e).reduce("", (seed, e) -> seed + e);
  }

  /// Returns an It spliting 's' with 'sep'.
  /// It is the inverse function of 'join'.
  public static function split (s: String, sep: String): It<String> {
    final len = s.length;
    final slen = sep.length;
    if (slen == 0)
      return It.fromString(s);

    var pos = 0;
    return new It(
      () -> pos <= len,
      () -> {
        var ix = s.indexOf(sep, pos);
        if (ix == -1)
          ix = len;

        final r = s.substring(pos, ix);
        pos = ix + slen;
        r;
      }
    );
  }

  // Eager ---------------------------------------------------------------------

  /// Returns 'true' if 'this' contains 'e' using 'feq'.
  /// If 'feq' is not defined, '==' is used.
  public function contains (e: T, ?feq: (T, T) -> Bool): Bool {
    if (feq == null) {
      while (hasNext())
        if (next() == e) return true;
    } else {
      while (hasNext())
        if (feq(next(), e)) return true;
    }
    return false;
  }

  /// Returns the number of elements of 'this'.
  public function count (): Int {
    var r = 0;
    while (hasNext()) {
      ++r;
      next();
    }
    return r;
  }

  /// Runs 'fn' witch each element of 'this'.
  public function each (fn: T->Void): Void {
    while(hasNext())
      fn(next());
  }

  /// Runs 'fn' witch each element of 'this', passing its index with each one.
  public function eachIx (fn: (T, Int)->Void): Void {
    var i = 0;
    while(hasNext())
      fn(next(), i++);
  }

  /// Runs 'fn' with each element of 'this' synchronously and after finishing
  /// executes 'g0'. If some fail happends execute 'fail(exception)' (if
  /// defined). For example:
  ///
  /// final is = [1, 2, 3];
  /// var sumTx3 = "";
  /// function cb3 (n:Int, frec: () -> Void): Void {
  ///   haxe.Timer.delay(() -> {
  ///     sumTx3 += "" + n;
  ///     frec();  //NOTE: frec must be called at the end of callback.
  ///   }, 100);
  /// }
  /// It.from(is).eachSyn(
  ///   cb3,
  ///   () -> t.eq(sumTx3, "123"),
  ///   (e) -> t.yes(false)
  /// );
  public function eachSyn<U> (
    fn: (T, (() -> Void)) -> Void,
    go: () -> Void,
    ?fail: (e:Dynamic) -> Void
  ) {
    function frec (): Void {
      if (hasNext()) {
        if (fail == null) {
          fn(next(), frec);
        } else {
          try {
            fn(next(), frec);
          } catch (e:Dynamic) {
            fail(e);
          }
        }
      } else {
        go();
      }
    }
    frec();
  }

  /// Returns 'true' if 'it' is equals to 'this' using the funcion 'feq'.
  /// If 'feq' is null or not is set, function '==' is used.
  public function eq (it: It<T>, ?feq: (T, T) -> Bool): Bool {
    if (feq == null) {
      while (hasNext()) {
        if (it.hasNext() && (next() == it.next())) continue;
        else return false;
      }
    } else {
      while (hasNext()) {
        if (it.hasNext() && feq(next(), it.next())) continue;
        else return false;
      }
    }
    return !it.hasNext();
  }

  /// Returns 'true' if every element of 'this' is 'true' with 'fn'.
  public function every (fn: (T) -> Bool): Bool {
    while (hasNext())
      if (!fn(next()))
        return false;
    return true;
  }

  /// Returns the first element which makes 'fn' 'true'.
  public function find (fn: T -> Bool): Option<T> {
    while (hasNext()) {
      final e = next();
      if (fn(e))
        return Some(e);
    }
    return None;
  }

  /// Returns the last element which makes 'fn' 'true'.
  public function findLast (fn: T -> Bool): Option<T> {
    var r = None;
    while (hasNext()) {
      final e = next();
      if (fn(e))
        r = Some(e);
    }
    return r;
  }

  /// Returns the first index of 'e' in 'this', or -1 if 'this' does not
  /// contains 'e',  using 'feq'.
  /// If 'feq' is not defined, '==' is used.
  public function index (e: T, ?feq: (T, T) -> Bool): Int {
    var c = 0;
    if (feq == null) {
      while (hasNext())
        if (next() == e) return c; else ++c;
    } else {
      while (hasNext())
        if (feq(next(), e)) return c; else ++c;
    }
    return -1;
  }

  /// Returns the index of the first element of 'this' that is 'true' with 'fn'
  /// or -1 if none matches the condition.
  public function indexf (fn: T -> Bool): Int {
    var c = 0;
    while (hasNext()) {
      if (fn(next()))
        return c;
      ++c;
    }
    return -1;
  }

  /// Implements Itereable interface.
  public function iterator (): Iterator<T> {
    return {
      hasNext: hasNext,
      next: next
    };
  }

  /// Returns the last index of 'e' in 'this', or -1 if 'this' does not
  /// contains 'e',  using 'feq'.
  /// If 'feq' is not defined, '==' is used.
  public function lastIndex (e: T, ?feq: (T, T) -> Bool): Int {
    var r = -1;
    var c = 0;
    if (feq == null) {
      while (hasNext())
        if (next() == e) r = c++; else ++c;
    } else {
      while (hasNext())
        if (feq(next(), e)) r = c++; else ++c;
    }
    return r;
  }

  /// Returns the last index of the first element of 'this' that is 'true' with
  /// 'fn' or -1 if none matches the condition.
  public function lastIndexf (fn: T -> Bool): Int {
    var r = -1;
    var c = 0;
    while (hasNext()) {
      if (fn(next()))
        r = c;
      ++c;
    }
    return r;
  }

  /// Returns the value resulting to apply 'fn' over 'seed' and the first
  /// element of 'this', and after that to apply 'fn' to the previous result
  /// in turn.
  /// 'reduce (x, It.empty())' returns 'x'.
  public function reduce<U> (seed: U, fn: (U, T) -> U): U {
    while (hasNext())
      seed = fn(seed, next());
    return seed;
  }

  /// Returns 'true' if al least one element of 'this' is 'true' with 'fn'.
  public function some (fn: T -> Bool): Bool {
    while (hasNext())
      if (fn(next()))
        return true;
    return false;
  }

  /// Returns an Array with elements of 'this' in the same order.
  public function to (): Array<T> {
    var r = new Array<T>();
    while (hasNext())
      r.push(next());
    return r;
  }

  /// Returns a representation of 'this'.
  public function toString (): String {
    var r = new StringBuf();
    r.add("It[");
    if (hasNext()) {
      r.add(Std.string(next()));
      while(hasNext()) {
        r.add(",");
        r.add(Std.string(next()));
      }
    }
    r.add("]");
    return r.toString();
  }

  /// Returns a Map from an It<Tp<String, V>> created with 'It.fromMap'.
  public function toMap<V> (): Option<Map<String, V>> {
    try {
      final it: It<Tp<String, V>> = cast(this);
      final r = new StringMap<V>();
      while (it.hasNext()) {
        final nx = it.next();
        r.set(nx.e1, nx.e2);
      }
      return cast(Some(r));
    } catch (e:Dynamic) {
      return None;
    }
  }

  // Lazy ----------------------------------------------------------------------

  /// Returns a new It concatenating 'this + it'.
  public function cat (it: It<T>): It<T> {
    return new It(
      () -> hasNext() || it.hasNext(),
      () -> hasNext() ? next() : it.next()
    );
  }

  /// Returns the rest of elements after do 'take'. The first element is
  /// the 'n' element.
  public function drop (n: Int): It<T> {
    var c = 0;
    while (c < n && hasNext()) {
      ++c;
      next();
    }
    return this;
  }

  /// Returns the rest of elements after do 'takeWhile'. The first element is
  /// an element such that 'fn(e) != true'.
  public function dropWhile (fn: T -> Bool): It<T> {
    var e;
    var nxt = hasNext();
    while (nxt) {
      e = next();
      if (!fn(e))
        break;
      nxt = hasNext();
    }
    return new It(
      () -> nxt,
      () -> {
        final r = e;
        nxt = hasNext();
        if (nxt)
          e = next();
        r;
      }
    );
  }

  /// Returns the rest of elements after do 'takeUntil'. The first element is
  /// an element such that 'fn(e) == true'.
  public function dropUntil (fn: T -> Bool): It<T> {
    var e;
    var nxt = hasNext();
    while (nxt) {
      e = next();
      if (fn(e))
        break;
      nxt = hasNext();
    }
    return new It(
      () -> nxt,
      () -> {
        final r = e;
        nxt = hasNext();
        if (nxt)
          e = next();
        r;
      }
    );
  }

  /// Returns elements which make 'fn' 'true'.
  public function filter (fn: (T) -> Bool): It<T> {
    var e: T;
    function goNext (): Bool {
      while (hasNext()) {
        e = next();
        if (fn(e))
          return true;
      }
      return false;
    }
    var nxt = goNext();
    return new It(
      () -> nxt,
      () -> {
        final r = e;
        nxt = goNext();
        r;
      }
    );
  }

  /// Returns a new It applying 'fn' to the first element and 'fn2' to the
  /// rest.
  /// If 'fn2' is not defined, 'fn' is applied to every element.
  public function map<U> (fn: T -> U, ?fn2: T -> U): It<U> {
    if (fn2 == null) {
      return new It(
        () -> hasNext(),
        () -> fn(next())
      );
    } else {
      var isFirst = true;
      return new It(
        () -> hasNext(),
        () ->
          if (isFirst) {
            isFirst = false;
            fn(next());
          } else {
            fn2(next());
          }
      );
    }
  }

  /// Returns a new It, adding an element at the end.
  public function push (e: T): It<T> {
    return cat(unary(e));
  }

  /// Returns the first 'n' elements of 'this'.
  public function take (n: Int): It<T> {
    var c = 0;
    return new It(
      () -> c < n && hasNext(),
      () -> {
        ++c;
        next();
      }
    );
  }

  /// Returns elements of 'this' while 'fn(e) == true'
  public function takeWhile (fn: T -> Bool): It<T> {
    var e;
    var nxt = hasNext();
    if (nxt) {
      e = next();
      return new It(
        () -> nxt && fn(e),
        () -> {
          final r = e;
          nxt = hasNext();
          if (nxt)
            e = next();
          r;
        }
      );
    }
    return It.empty();
  }

  /// Returns elements of 'this' while 'fn(e) != true'
  public function takeUntil (fn: T -> Bool): It<T> {
    var e;
    var nxt = hasNext();
    if (nxt) {
      e = next();
      return new It(
        () -> nxt && !fn(e),
        () -> {
          final r = e;
          nxt = hasNext();
          if (nxt)
            e = next();
          r;
        }
      );
    }
    return It.empty();
  }

  /// Returns a nes It, adding an element at the beginning.
  public function unshift (e: T): It<T> {
    return unary(e).cat(this);
  }

  // With intermediate Array ---------------------------------------------------

  /// Returns elements of 'this' in reverse order.
  /// It creates a temporary array.
  public function reverse (): It<T> {
    var tmp = to();
    tmp.reverse();
    return It.from(tmp);
  }

  /// Returns elements of 'this' sorted by 'fn'.
  /// It creates a temporary array.
  public function sort (fn: (T, T) -> Int): It<T> {
    var tmp = to();
    tmp.sort(fn);
    return It.from(tmp);
  }

  /// Returns elements of 'this' in random order.
  /// It creates a temporary array.
  public function shuffle (): It<T> {
    final a = to();
    Rnd.shuffle(a);
    return It.from(a);
  }

  /// Returns a tuple of It over the corresponding first and second element
  /// of 'it'.
  /// It creates two temporary arrays.
  public static function unzip<T, U> (it: It<Tp<T, U>>): Tp<It<T>, It<U>> {
    var a1 = [];
    var a2 = [];
    for (tp in it) {
      a1.push(tp.e1);
      a2.push(tp.e2);
    }
    return new Tp(It.from(a1), It.from(a2));
  }

  /// Returns a tuple of It over the corresponding first, second and thirt
  /// element of 'it'.
  /// It creates three temporary arrays.
  public static function unzip3<T, U, Z> (
    it: It<Tp3<T, U, Z>>
  ): Tp3<It<T>, It<U>, It<Z>> {
    var a1 = [];
    var a2 = [];
    var a3 = [];
    for (tp3 in it) {
      a1.push(tp3.e1);
      a2.push(tp3.e2);
      a3.push(tp3.e3);
    }
    return new Tp3(It.from(a1), It.from(a2), It.from(a3));
  }

}

