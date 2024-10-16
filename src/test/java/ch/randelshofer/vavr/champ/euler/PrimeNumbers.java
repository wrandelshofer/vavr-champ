/* ____  ______________  ________________________  __________
 * \   \/   /      \   \/   /   __/   /      \   \/   /      \
 *  \______/___/\___\______/___/_____/___/\___\______/___/\___\
 *
 * The MIT License (MIT)
 *
 * Copyright 2024 Vavr, https://vavr.io
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package ch.randelshofer.vavr.champ.euler;

import ch.randelshofer.vavr.champ.ChampMap;
import io.vavr.Tuple;
import io.vavr.collection.Set;
import io.vavr.collection.Stream;
import io.vavr.collection.TreeSet;

final class PrimeNumbers {

    private static final Set<Integer> PRIMES_2_000_000 = Sieve.fillSieve(2_000_000, TreeSet.empty());

    private PrimeNumbers() {
    }

    static ChampMap<Long, Long> factorization(long num) {
        if (num == 1) {
            return ChampMap.empty();
        } else {
            return primeFactors(num)
                    .map(p -> ChampMap.of(Tuple.of(p, 1L))
                            .merge(factorization(num / p), (a, b) -> a + b))
                    .getOrElse(ChampMap::empty);
        }
    }

    static Stream<Long> primeFactors(long num) {
        return Stream.rangeClosed(2L, (int) Math.sqrt(num))
                .find(d -> num % d == 0)
                .map(d -> Stream.cons(d, () -> primeFactors(num / d)))
                .getOrElse(() -> Stream.of(num));
    }

    static Stream<Integer> primes() {
        return Stream.ofAll(PRIMES_2_000_000);
    }
}
