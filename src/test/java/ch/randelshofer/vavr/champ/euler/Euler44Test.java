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

import io.vavr.API;
import io.vavr.concurrent.Future;
import org.junit.jupiter.api.Test;

import java.util.concurrent.TimeUnit;

import static org.assertj.core.api.Assertions.assertThat;

public class Euler44Test {

    /**
     * <strong>Problem 44 Pentagon numbers</strong>
     * <p>
     * Pentagonal numbers are generated by the formula, P<sub><i>n</i></sub>=<i>n</i>(3<i>n</i>−1)/2.
     * The first ten pentagonal numbers are: </p>
     * <p>
     *     1, 5, 12, 22, 35, 51, 70, 92, 117, 145, ...
     * </p>
     * <p>
     * It can be seen that P<sub>4</sub> + P<sub>7</sub> = 22 + 70 = 92 = P<sub>8</sub>.
     * However, their difference, 70 − 22 = 48, is not pentagonal.
     * </p>
     * <p>
     * Find the pair of pentagonal numbers, P<sub><i>j</i></sub> and P<sub><i>k</i></sub>,
     * for which their sum and difference are pentagonal and D = |P<sub><i>k</i></sub> - P<sub><i>j</i></sub>|
     * is minimised; what is the value of D?
     * <p>
     * See also <a href="https://projecteuler.net/problem=44">projecteuler.net
     * problem 44</a>.
     */
    @Test
    public void shouldSolveProblem44() {
        final Future<Long> computation = API.Future(this::minimalPentagonalDiff)
                .await(2, TimeUnit.SECONDS);
        assertThat(computation.getOrElse(-1L)).isEqualTo(5482660);
    }

    private Long minimalPentagonalDiff() {
        return Utils.pentagonal().flatMap(sumPentagonal ->
                Utils.pentagonal().takeWhile(pentagonal -> sumPentagonal.compareTo(pentagonal) > 0)
                        .filter(pj -> Utils.isPentagonal(sumPentagonal - pj) &&
                                Utils.isPentagonal(sumPentagonal - 2 * pj))
                        .map(pj -> sumPentagonal - 2 * pj)).head();
    }
}
