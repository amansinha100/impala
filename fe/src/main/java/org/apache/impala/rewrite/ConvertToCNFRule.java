// Licensed to the Apache Software Foundation (ASF) under one
// or more contributor license agreements.  See the NOTICE file
// distributed with this work for additional information
// regarding copyright ownership.  The ASF licenses this file
// to you under the Apache License, Version 2.0 (the
// "License"); you may not use this file except in compliance
// with the License.  You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations
// under the License.

package org.apache.impala.rewrite;

import org.apache.impala.analysis.Analyzer;
import org.apache.impala.analysis.BetweenPredicate;
import org.apache.impala.analysis.BinaryPredicate;
import org.apache.impala.analysis.CompoundPredicate;
import org.apache.impala.analysis.Expr;
import org.apache.impala.analysis.Predicate;
import org.apache.impala.analysis.TupleId;

import java.util.ArrayList;
import java.util.List;


public class ConvertToCNFRule implements ExprRewriteRule {
  public static ExprRewriteRule INSTANCE = new ConvertToCNFRule(true);
  public static ExprRewriteRule TEST_INSTANCE = new ConvertToCNFRule(false);

  // flag that convert a disjunct to CNF only if the predicate involves
  // 2 or more tables. By default, we do this only for multi table case
  // but for unit testing it is useful to disable this
  private boolean forMultiTablesOnly_ = true;

  @Override
  public Expr apply(Expr expr, Analyzer analyzer) {
    return convertToCNF(expr);
  }

  /**
   * Convert a predicate to conjunctive normal form (CNF). By default, we
   * do this conversion if the expressions in the predicate reference 2 or
   * more tuples but depending on the forMultiTablesOnly flag, it can work
   * for single table predicates also (primarily intended for testing).
   * Converting to CNF may allow pushdown of certain conjuncts to
   * the underlying table which would otherwise have been only evaluated by
   * the join operator.
   *
   * Currently, this rule handles the following common patterns (in the future
   * more patterns may be added):
   *  1.
   *  original: (a AND b) OR c
   *  rewritten: (a OR c) AND (b OR c)
   *  2.
   *  if 'c' is another compound predicate, a subsequent application of this
   *  rule would again convert to CNF:
   *  original: (a AND b) OR (c AND d)
   *  first rewrite: (a OR (c AND d)) AND (b OR (c AND d))
   *  subsequent rewrite: (a OR c) AND (a OR d) AND (b OR c) AND (b OR d)
   *  3.
   *  original: NOT(a OR b)
   *  rewritten: NOT(a) AND NOT(b)  (by De Morgan's theorem)
   *
   *  Following predicates are already in CNF, so no conversion is done:
   *   a OR b where 'a' and 'b' are not CompoundPredicates
   *   a AND b
   *
   * @param pred
   * @return a CNF expression
   */
  private Expr convertToCNF(Expr pred) {
    if (!(pred instanceof CompoundPredicate)) {
      return pred;
    }
    CompoundPredicate cpred = (CompoundPredicate) pred;
    if (cpred.getOp() == CompoundPredicate.Operator.AND) {
      // this is already a conjunct
      return cpred;
    } else if (cpred.getOp() == CompoundPredicate.Operator.OR) {
      if (forMultiTablesOnly_) {
        // check if this predicate reference one or more tuples. If only 1 tuple,
        // we can skip the rewrite since the disjunct can be pushed down as-is
        List<TupleId> tids = new ArrayList<>();
        cpred.getIds(tids, null);
        if (tids.size() <= 1) {
          return cpred;
        }
      }
      Expr lhs = cpred.getChild(0);
      Expr rhs = cpred.getChild(1);
      if (lhs instanceof CompoundPredicate &&
              ((CompoundPredicate)lhs).getOp() == CompoundPredicate.Operator.AND) {
        // predicate: (a AND b) OR c
        // convert to (a OR c) AND (b OR c)
        List<Expr> disjuncts = new ArrayList<>();
        disjuncts.add(lhs.getChild(0));
        disjuncts.add(rhs);
        Expr lhs1 = (CompoundPredicate) CompoundPredicate.createDisjunctivePredicate(disjuncts);
        disjuncts.clear();
        disjuncts.add(lhs.getChild(1));
        disjuncts.add(rhs);
        Expr rhs1 = (CompoundPredicate) CompoundPredicate.createDisjunctivePredicate(disjuncts);
        Predicate newPredicate = (CompoundPredicate) CompoundPredicate.createConjunction(lhs1, rhs1);
        return newPredicate;
      } else if (rhs instanceof CompoundPredicate &&
              ((CompoundPredicate)rhs).getOp() == CompoundPredicate.Operator.AND) {
        // predicate: a OR (b AND c)
        // convert to (a OR b) AND (a or c)
        List<Expr> disjuncts = new ArrayList<>();
        disjuncts.add(lhs);
        disjuncts.add(rhs.getChild(0));
        Expr lhs1 = (CompoundPredicate) CompoundPredicate.createDisjunctivePredicate(disjuncts);
        disjuncts.clear();
        disjuncts.add(lhs);
        disjuncts.add(rhs.getChild(1));
        Expr rhs1 = (CompoundPredicate) CompoundPredicate.createDisjunctivePredicate(disjuncts);
        Predicate newPredicate = (CompoundPredicate) CompoundPredicate.createConjunction(lhs1, rhs1);
        return newPredicate;
      }

    } else if (cpred.getOp() == CompoundPredicate.Operator.NOT) {
      Expr child = cpred.getChild(0);
      if (child instanceof CompoundPredicate &&
              ((CompoundPredicate)child).getOp() == CompoundPredicate.Operator.OR) {
        if (forMultiTablesOnly_) {
          // check if this predicate reference one or more tuples. If only 1 tuple,
          // we can skip the rewrite since the disjunct can be pushed down as-is
          List<TupleId> tids = new ArrayList<>();
          child.getIds(tids, null);
          if (tids.size() <= 1) {
            return cpred;
          }
        }
        // predicate: NOT (a OR b)
        // convert to: NOT(a) AND NOT(b)
        Expr lhs = ((CompoundPredicate) child).getChild(0);
        Expr rhs = ((CompoundPredicate) child).getChild(1);
        Expr lhs1 = new CompoundPredicate(CompoundPredicate.Operator.NOT, lhs, null);
        Expr rhs1 = new CompoundPredicate(CompoundPredicate.Operator.NOT, rhs, null);
        Predicate newPredicate = (CompoundPredicate) CompoundPredicate.createConjunction(lhs1, rhs1);
        return newPredicate;
      }

    }
    return pred;
  }

  private ConvertToCNFRule(boolean forMultiTablesOnly) {
    forMultiTablesOnly_ = forMultiTablesOnly;
  }
}
