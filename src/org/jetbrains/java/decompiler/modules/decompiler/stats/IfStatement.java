// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.modules.decompiler.stats;

import org.jetbrains.java.decompiler.main.DecompilerContext;
import org.jetbrains.java.decompiler.modules.decompiler.DecHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ExprProcessor;
import org.jetbrains.java.decompiler.modules.decompiler.StatEdge;
import org.jetbrains.java.decompiler.modules.decompiler.SecondaryFunctionsHelper;
import org.jetbrains.java.decompiler.modules.decompiler.ValidationHelper;
import org.jetbrains.java.decompiler.modules.decompiler.exps.*;
import org.jetbrains.java.decompiler.modules.decompiler.exps.FunctionExprent.FunctionType;
import org.jetbrains.java.decompiler.struct.match.IMatchable;
import org.jetbrains.java.decompiler.struct.match.MatchEngine;
import org.jetbrains.java.decompiler.struct.match.MatchNode;
import org.jetbrains.java.decompiler.util.StartEndPair;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.jetbrains.java.decompiler.util.TextUtil;

import java.util.ArrayList;
import java.util.List;


public class IfStatement extends Statement {

  public static final int IFTYPE_IF = 0;
  public static final int IFTYPE_IFELSE = 1;

  public int iftype;

  // *****************************************************************************
  // private fields
  // *****************************************************************************

  private Statement ifstat;
  private Statement elsestat;

  private StatEdge ifedge;
  private StatEdge elseedge;

  private boolean negated = false;
  private boolean patternMatched = false;

  private boolean hasPPMM = false;

  // RTF: tracks whether IfHelper transformations have flipped the condition
  // from the original bytecode branch direction. Toggled each time a
  // transformation wraps the condition in BOOL_NOT. The post-pass uses this
  // to swap if/else bodies back to the correct parity.
  private boolean rtfConditionFlipped = false;

  // RTF: tracks whether the current if-body corresponds to the original
  // bytecode fall-through path. At construction, ifstat = jump target (false).
  // Toggled on every body swap so the layout pass can match javac's block order.
  private boolean rtfIfBodyIsFallThrough = false;

  // RTF: true when the original bytecode used a 2-instruction branch pattern
  // (ifXX + goto) where the condition-true path was the fall-through to a goto.
  // At render time, emit if(inverted){} else{body} to reproduce the pattern.
  private boolean rtfOriginalHadGotoFallthrough = false;

  private final List<Exprent> headexprent = new ArrayList<>(1); // contains IfExprent

  // *****************************************************************************
  // constructors
  // *****************************************************************************

  protected IfStatement() {
    super(StatementType.IF);

    headexprent.add(null);
  }

  protected IfStatement(Statement head, int regedges, Statement postst) {

    this();

    first = head;
    stats.addWithKey(head, head.id);

    List<StatEdge> lstHeadSuccs = head.getSuccessorEdges(STATEDGE_DIRECT_ALL);

    switch (regedges) {
      case 0:
        ifstat = null;
        elsestat = null;

        break;
      case 1:
        ifstat = null;
        elsestat = null;

        StatEdge edgeif = lstHeadSuccs.get(1);
        if (edgeif.getType() != StatEdge.TYPE_REGULAR) {
          post = lstHeadSuccs.get(0).getDestination();
        }
        else {
          post = edgeif.getDestination();
          negated = true;
        }
        break;
      case 2:
        elsestat = lstHeadSuccs.get(0).getDestination();  // fall-through
        ifstat = lstHeadSuccs.get(1).getDestination();    // jump target
        rtfIfBodyIsFallThrough = false;  // ifstat is the jump target

        List<StatEdge> lstSucc = ifstat.getSuccessorEdges(StatEdge.TYPE_REGULAR);
        List<StatEdge> lstSucc1 = elsestat.getSuccessorEdges(StatEdge.TYPE_REGULAR);

        if (ifstat.getPredecessorEdges(StatEdge.TYPE_REGULAR).size() > 1 || lstSucc.size() > 1) {
          post = ifstat;
        }
        else if (elsestat.getPredecessorEdges(StatEdge.TYPE_REGULAR).size() > 1 || lstSucc1.size() > 1) {
          post = elsestat;
        }
        else {
          if (lstSucc.size() == 0) {
            post = elsestat;
          }
          else if (lstSucc1.size() == 0) {
            post = ifstat;
          }
        }

        if (ifstat == post) {
          if (elsestat != post) {
            ifstat = elsestat;  // ifstat is now the fall-through path
            negated = true;
            rtfIfBodyIsFallThrough = true;
            // The original had: ifXX TARGET (jump over body); body; goto END
            // This is the 2-instruction pattern that collapseElse will simplify
            rtfOriginalHadGotoFallthrough = true;
          }
          else {
            ifstat = null;
          }
          elsestat = null;
        }
        else if (elsestat == post) {
          elsestat = null;
        }
        else {
          post = postst;
        }

        if (elsestat == null) {
          regedges = 1;  // if without else
        }
    }

    ifedge = lstHeadSuccs.get(negated ? 0 : 1);
    elseedge = (regedges == 2) ? lstHeadSuccs.get(negated ? 1 : 0) : null;

    iftype = (regedges == 2) ? IFTYPE_IFELSE : IFTYPE_IF;

    if (iftype == IFTYPE_IF) {
      if (regedges == 0) {
        StatEdge edge = lstHeadSuccs.get(0);
        head.removeSuccessor(edge);
        edge.setSource(this);
        this.addSuccessor(edge);
      }
      else if (regedges == 1) {
        StatEdge edge = lstHeadSuccs.get(negated ? 1 : 0);
        head.removeSuccessor(edge);
      }
    }

    if (ifstat != null) {
      stats.addWithKey(ifstat, ifstat.id);
    }

    if (elsestat != null) {
      stats.addWithKey(elsestat, elsestat.id);
    }

    if (post == head) {
      post = this;
    }
  }


  // *****************************************************************************
  // public methods
  // *****************************************************************************

  public static Statement isHead(Statement head) {

    if (head instanceof BasicBlockStatement && head.getLastBasicType() == LastBasicType.IF) {
      int regsize = head.getSuccessorEdges(StatEdge.TYPE_REGULAR).size();

      Statement p = null;

      boolean ok = (regsize < 2);
      if (!ok) {
        List<Statement> lst = new ArrayList<>();
        if (DecHelper.isChoiceStatement(head, lst)) {
          p = lst.remove(0);

          for (Statement st : lst) {
            if (st.isMonitorEnter()) {
              return null;
            }
          }

          ok = DecHelper.checkStatementExceptions(lst);
        }
      }

      if (ok) {
        return new IfStatement(head, regsize, p);
      }
    }

    return null;
  }

  @Override
  public TextBuffer toJava(int indent) {
    TextBuffer buf = new TextBuffer();

    buf.append(ExprProcessor.listToJava(varDefinitions, indent));

    buf.append(first.toJava(indent));

    if (isLabeled()) {
      buf.appendIndent(indent).append("label").append(this.id).append(":").appendLineSeparator();
    }

    Exprent condition = headexprent.get(0);

    // RTF: when the original bytecode used ifXX+goto (2-instruction pattern),
    // render as if(inverted){} else{body} so javac reproduces the same pattern.
    if (DecompilerContext.isRoundtripFidelity() && rtfOriginalHadGotoFallthrough
        && iftype == IFTYPE_IF && ifstat != null && elsestat == null && condition instanceof IfExprent) {
      IfExprent ifExpr = (IfExprent) condition;
      Exprent innerCond = ifExpr.getCondition();
      // For compound conditions (&&), split the first operand and render as
      // if(!(first)){} else if(rest){body} so javac emits the 2-instruction
      // pattern only for the first sub-condition without affecting the rest.
      if (innerCond instanceof FunctionExprent
          && ((FunctionExprent) innerCond).getFuncType() == FunctionExprent.FunctionType.BOOLEAN_AND) {
        List<Exprent> operands = ((FunctionExprent) innerCond).getLstOperands();
        if (operands.size() >= 2) {
          // Negate the first operand for the empty-if
          Exprent firstOp = operands.get(0);
          FunctionExprent negFirst = new FunctionExprent(FunctionExprent.FunctionType.BOOL_NOT, firstOp, null);
          Exprent simplified = SecondaryFunctionsHelper.propagateBoolNot(negFirst);
          Exprent negatedFirst = simplified != null ? simplified : negFirst;
          // Build the remaining condition (second operand onward)
          Exprent restCond;
          if (operands.size() == 2) {
            restCond = operands.get(1);
          } else {
            restCond = new FunctionExprent(FunctionExprent.FunctionType.BOOLEAN_AND,
                new ArrayList<>(operands.subList(1, operands.size())), null);
          }
          buf.appendIndent(indent);
          buf.append("if (").append(negatedFirst.toJava(indent)).append(") {").appendLineSeparator();
          buf.appendIndent(indent).append("} else if (").append(restCond.toJava(indent)).append(") {").appendLineSeparator();
          buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, true));
          buf.appendIndent(indent).append("}").appendLineSeparator();
          return buf;
        }
      }
      // Simple condition: negate the whole condition for the empty-if form
      IfExprent negated = (IfExprent) ifExpr.copy();
      negated.negateIf();
      buf.appendIndent(indent);
      buf.append(negated.toJava(indent));
      buf.append(" {").appendLineSeparator();
      buf.appendIndent(indent).append("} else {").appendLineSeparator();
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, true));
      buf.appendIndent(indent).append("}").appendLineSeparator();
      return buf;
    }

    // RTF: use originalBytecodeType to detect and fix comparison operator mismatches.
    if (DecompilerContext.isRoundtripFidelity() && !rtfOriginalHadGotoFallthrough
        && condition instanceof IfExprent) {
      IfExprent ifExpr = (IfExprent) condition;
      IfExprent.Type origType = ifExpr.getOriginalBytecodeType();
      if (origType != null) {
        FunctionType expectedFT = origType.getNegative().getFunctionType();
        if (expectedFT != null) {
          Exprent innerCond = ifExpr.getCondition();
          FunctionType effectiveFT = rtfGetEffectiveComparisonType(innerCond);
          if (effectiveFT != null && effectiveFT != expectedFT) {
            Exprent correctedCond = rtfBuildCorrectedCondition(innerCond, expectedFT);
            if (correctedCond != null) {
              if (iftype == IFTYPE_IF && ifstat != null && elsestat == null) {
                // IFTYPE_IF: use the empty-then trick.
                // if (correct) {} else { body } preserves semantics because
                // correct is the negation of current.
                IfExprent wrapper = (IfExprent) ifExpr.copy();
                wrapper.setCondition(correctedCond);
                buf.appendIndent(indent);
                buf.append(wrapper.toJava(indent));
                buf.append(" {").appendLineSeparator();
                buf.appendIndent(indent).append("} else {").appendLineSeparator();
                buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, true));
                buf.appendIndent(indent).append("}").appendLineSeparator();
                return buf;
              } else if (iftype == IFTYPE_IFELSE && ifstat != null && elsestat != null) {
                // IFTYPE_IFELSE: swap bodies and fix the operator.
                // if (correct) { elseBody } else { ifBody } preserves semantics.
                IfExprent wrapper = (IfExprent) ifExpr.copy();
                wrapper.setCondition(correctedCond);
                buf.appendIndent(indent);
                buf.append(wrapper.toJava(indent));
                buf.append(" {").appendLineSeparator();
                buf.append(ExprProcessor.jmpWrapper(elsestat, indent + 1, true));

                // Render else branch with the original if-body
                boolean elseif = false;
                if (ifstat instanceof IfStatement
                    && ifstat.varDefinitions.isEmpty()
                    && (ifstat.getFirst().getExprents() != null && ifstat.getFirst().getExprents().isEmpty())
                    && !ifstat.isLabeled()
                    && (ifstat.getSuccessorEdges(STATEDGE_DIRECT_ALL).isEmpty()
                        || !ifstat.getSuccessorEdges(STATEDGE_DIRECT_ALL).get(0).explicit)) {
                  buf.appendIndent(indent).append("} else ");
                  TextBuffer content = ExprProcessor.jmpWrapper(ifstat, indent, false);
                  content.setStart(TextUtil.getIndentString(indent).length());
                  buf.append(content);
                  elseif = true;
                } else {
                  TextBuffer content = ExprProcessor.jmpWrapper(ifstat, indent + 1, false);
                  if (content.length() > 0) {
                    buf.appendIndent(indent).append("} else {").appendLineSeparator();
                    buf.append(content);
                  }
                }
                if (!elseif) {
                  buf.appendIndent(indent).append("}").appendLineSeparator();
                }
                return buf;
              }
            }
          }
        }
      }
    }

    buf.appendIndent(indent);
    // Condition can be null in early processing stages
    if (condition != null) {
      buf.append(condition.toJava(indent));
    } else {
      buf.append("if <null condition>");
    }
    buf.append(" {").appendLineSeparator();

    if (ifstat == null) {
      boolean semicolon = false;
      if (ifedge.explicit) {
        semicolon = true;
        if (ifedge.getType() == StatEdge.TYPE_BREAK) {
          // break
          buf.appendIndent(indent + 1).append("break");
        }
        else {
          // continue
          buf.appendIndent(indent + 1).append("continue");
        }

        if (ifedge.labeled) {
          buf.append(" label").append(ifedge.closure == null ? "<unknownclosure>" : Integer.toString(ifedge.closure.id));
        }
      }
      if(semicolon) {
        buf.append(";").appendLineSeparator();
      }
    }
    else {
      buf.append(ExprProcessor.jmpWrapper(ifstat, indent + 1, true));
    }

    boolean elseif = false;

    if (elsestat != null) {
      if (elsestat instanceof IfStatement
          && elsestat.varDefinitions.isEmpty() && (elsestat.getFirst().getExprents() != null && elsestat.getFirst().getExprents().isEmpty()) &&
          !elsestat.isLabeled() &&
          (elsestat.getSuccessorEdges(STATEDGE_DIRECT_ALL).isEmpty()
           || !elsestat.getSuccessorEdges(STATEDGE_DIRECT_ALL).get(0).explicit)) { // else if
        buf.appendIndent(indent).append("} else ");

        TextBuffer content = ExprProcessor.jmpWrapper(elsestat, indent, false);
        content.setStart(TextUtil.getIndentString(indent).length());
        buf.append(content);

        elseif = true;
      }
      else {
        TextBuffer content = ExprProcessor.jmpWrapper(elsestat, indent + 1, false);

        if (content.length() > 0) {
          buf.appendIndent(indent).append("} else {").appendLineSeparator();
          buf.append(content);
        }
      }
    }

    if (!elseif) {
      buf.appendIndent(indent).append("}").appendLineSeparator();
    }

    return buf;
  }

  @Override
  public void initExprents() {
    IfExprent ifexpr = (IfExprent)first.getExprents().remove(first.getExprents().size() - 1);

    if (negated) {
      ifexpr = (IfExprent)ifexpr.copy();
      ifexpr.negateIf();
    }

    headexprent.set(0, ifexpr);
  }

  @Override
  public List<Object> getSequentialObjects() {

    List<Object> lst = new ArrayList<>(stats);
    lst.add(1, headexprent.get(0));

    return lst;
  }

  @Override
  public void replaceExprent(Exprent oldexpr, Exprent newexpr) {
    if (headexprent.get(0) == oldexpr) {
      headexprent.set(0, newexpr);
    }
  }

  @Override
  public void replaceStatement(Statement oldstat, Statement newstat) {
    super.replaceStatement(oldstat, newstat);

    if (ifstat == oldstat) {
      ifstat = newstat;
    }

    if (elsestat == oldstat) {
      elsestat = newstat;
    }

    List<StatEdge> lstSuccs = first.getSuccessorEdges(STATEDGE_DIRECT_ALL);

    if (iftype == IFTYPE_IF) {
      ifedge = lstSuccs.get(0);
      elseedge = null;
    }
    else {
      StatEdge edge0 = lstSuccs.get(0);
      StatEdge edge1 = lstSuccs.get(1);
      if (edge0.getDestination() == ifstat) {
        ifedge = edge0;
        elseedge = edge1;
      }
      else {
        ifedge = edge1;
        elseedge = edge0;
      }
    }
  }

  @Override
  public boolean hasBasicSuccEdge() {
    return iftype == IFTYPE_IF;
  }

  @Override
  public Statement getSimpleCopy() {
    IfStatement is = new IfStatement();
    is.iftype = this.iftype;
    is.negated = this.negated;
    is.rtfConditionFlipped = this.rtfConditionFlipped;
    is.rtfIfBodyIsFallThrough = this.rtfIfBodyIsFallThrough;

    return is;
  }

  @Override
  public void initSimpleCopy() {
    first = stats.get(0);

    List<StatEdge> lstSuccs = first.getSuccessorEdges(STATEDGE_DIRECT_ALL);
    ifedge = lstSuccs.get((iftype == IFTYPE_IF || negated) ? 0 : 1);
    if (stats.size() > 1) {
      ifstat = stats.get(1);
    }

    if (iftype == IFTYPE_IFELSE) {
      elseedge = lstSuccs.get(negated ? 1 : 0);
      elsestat = stats.get(2);
    }
  }

  // *****************************************************************************
  // getter and setter methods
  // *****************************************************************************

  public Statement getElsestat() {
    return elsestat;
  }

  public void setElsestat(Statement elsestat) {
    this.elsestat = elsestat;
  }

  public Statement getIfstat() {
    return ifstat;
  }

  public void setIfstat(Statement ifstat) {
    this.ifstat = ifstat;
  }

  public boolean isNegated() {
    return negated;
  }

  public void setNegated(boolean negated) {
    this.negated = negated;
  }

  public List<Exprent> getHeadexprentList() {
    return headexprent;
  }

  public IfExprent getHeadexprent() {
    return (IfExprent)headexprent.get(0);
  }

  public void setElseEdge(StatEdge elseedge) {
    this.elseedge = elseedge;
  }

  public void setIfEdge(StatEdge ifedge) {
    this.ifedge = ifedge;
  }

  public StatEdge getIfEdge() {
    return ifedge;
  }

  public StatEdge getElseEdge() {
    return elseedge;
  }

  public boolean isPatternMatched() {
    return patternMatched;
  }

  public void setPatternMatched(boolean patternMatched) {
    this.patternMatched = patternMatched;
  }

  public boolean hasPPMM() {
    return hasPPMM;
  }

  public void setHasPPMM(boolean hasPPMM) {
    this.hasPPMM = hasPPMM;
  }

  public boolean isRtfOriginalHadGotoFallthrough() {
    return rtfOriginalHadGotoFallthrough;
  }

  public boolean isRtfConditionFlipped() {
    return rtfConditionFlipped;
  }

  public void setRtfConditionFlipped(boolean rtfConditionFlipped) {
    this.rtfConditionFlipped = rtfConditionFlipped;
  }

  public void toggleRtfConditionFlipped() {
    this.rtfConditionFlipped = !this.rtfConditionFlipped;
  }

  public boolean isRtfIfBodyIsFallThrough() {
    return rtfIfBodyIsFallThrough;
  }

  public void toggleRtfIfBodyIsFallThrough() {
    this.rtfIfBodyIsFallThrough = !this.rtfIfBodyIsFallThrough;
  }

  @Override
  public List<VarExprent> getImplicitlyDefinedVars() {
    List<VarExprent> vars = new ArrayList<>();

    List<Exprent> conditionList = getHeadexprent().getCondition().getAllExprents(true);
    conditionList.add(getHeadexprent().getCondition());

    for (Exprent condition : conditionList) {
      if (condition instanceof FunctionExprent func) {
        // Pattern match variable is implicitly defined
        if (func.getFuncType() == FunctionType.INSTANCEOF && func.getLstOperands().size() > 2) {
          vars.addAll(((Pattern) func.getLstOperands().get(2)).getPatternVars());
        }
      }
    }

    return vars;
  }

  @Override
  public StartEndPair getStartEndRange() {
    return StartEndPair.join(super.getStartEndRange(),
      ifstat != null ? ifstat.getStartEndRange() : null,
      elsestat != null ? elsestat.getStartEndRange(): null);
  }

  // *****************************************************************************
  // IMatchable implementation
  // *****************************************************************************

  @Override
  public IMatchable findObject(MatchNode matchNode, int index) {
    IMatchable object = super.findObject(matchNode, index);
    if (object != null) {
      return object;
    }

    if (matchNode.getType() == MatchNode.MATCHNODE_EXPRENT) {
      String position = (String)matchNode.getRuleValue(MatchProperties.EXPRENT_POSITION);
      if ("head".equals(position)) {
        return getHeadexprent();
      }
    }

    return null;
  }

  @Override
  public boolean match(MatchNode matchNode, MatchEngine engine) {
    if (!super.match(matchNode, engine)) {
      return false;
    }

    Integer type = (Integer) matchNode.getRuleValue(MatchProperties.STATEMENT_IFTYPE);
    return type == null || this.iftype == type;
  }

  /**
   * RTF: extract the effective comparison FunctionType from a condition expression.
   * Handles direct comparisons (EQ..LE) and BOOL_NOT wrapped comparisons.
   * Returns null if the condition is not a recognizable simple comparison.
   */
  private static FunctionType rtfGetEffectiveComparisonType(Exprent cond) {
    if (!(cond instanceof FunctionExprent)) {
      return null;
    }
    FunctionExprent func = (FunctionExprent) cond;
    FunctionType ft = func.getFuncType();

    // Direct comparison (EQ, NE, LT, GE, GT, LE)
    if (ft.ordinal() >= FunctionType.EQ.ordinal()
        && ft.ordinal() <= FunctionType.LE.ordinal()) {
      return ft;
    }

    // BOOL_NOT wrapping a comparison: !(a == b) effectively is NE
    if (ft == FunctionType.BOOL_NOT && func.getLstOperands().size() == 1) {
      Exprent inner = func.getLstOperands().get(0);
      if (inner instanceof FunctionExprent) {
        FunctionType innerFt = ((FunctionExprent) inner).getFuncType();
        if (innerFt.ordinal() >= FunctionType.EQ.ordinal()
            && innerFt.ordinal() <= FunctionType.LE.ordinal()) {
          // The effective type is the negation of the inner comparison.
          // Use IfExprent.Type mapping to get the negation.
          IfExprent.Type mapped = rtfFunctionTypeToIfType(innerFt);
          if (mapped != null) {
            return mapped.getNegative().getFunctionType();
          }
        }
      }
    }

    return null;
  }

  /**
   * RTF: build a corrected condition expression that uses the expected FunctionType.
   * For direct comparisons, replaces the operator. For BOOL_NOT wrapped comparisons,
   * unwraps and adjusts the inner operator.
   * Returns null if the condition cannot be corrected.
   */
  private static Exprent rtfBuildCorrectedCondition(Exprent cond, FunctionType expectedFT) {
    if (!(cond instanceof FunctionExprent)) {
      return null;
    }
    FunctionExprent func = (FunctionExprent) cond;
    FunctionType ft = func.getFuncType();

    // Direct comparison: just swap the operator
    if (ft.ordinal() >= FunctionType.EQ.ordinal()
        && ft.ordinal() <= FunctionType.LE.ordinal()) {
      return new FunctionExprent(expectedFT, func.getLstOperands(), func.bytecode);
    }

    // BOOL_NOT wrapping a comparison: build a direct comparison with the expected operator
    if (ft == FunctionType.BOOL_NOT && func.getLstOperands().size() == 1) {
      Exprent inner = func.getLstOperands().get(0);
      if (inner instanceof FunctionExprent) {
        FunctionExprent innerFunc = (FunctionExprent) inner;
        FunctionType innerFt = innerFunc.getFuncType();
        if (innerFt.ordinal() >= FunctionType.EQ.ordinal()
            && innerFt.ordinal() <= FunctionType.LE.ordinal()) {
          return new FunctionExprent(expectedFT, innerFunc.getLstOperands(), innerFunc.bytecode);
        }
      }
    }

    return null;
  }

  /** Map a FunctionType comparison operator to the corresponding IfExprent.Type for negation lookup. */
  private static IfExprent.Type rtfFunctionTypeToIfType(FunctionType ft) {
    switch (ft) {
      case EQ: return IfExprent.Type.EQ;
      case NE: return IfExprent.Type.NE;
      case LT: return IfExprent.Type.LT;
      case GE: return IfExprent.Type.GE;
      case GT: return IfExprent.Type.GT;
      case LE: return IfExprent.Type.LE;
      default: return null;
    }
  }

  public void fixIfInvariantEmptyElseBranch() {
    // if(){...}else{;} -> if(){...}

    Statement elseStat = this.getElsestat();

    if (this.iftype != IfStatement.IFTYPE_IFELSE ||
        elseStat.type != StatementType.BASIC_BLOCK ||
        elseStat.getExprents() == null ||
        !elseStat.getExprents().isEmpty()) {
      return;
    }

    // Degrade to an if statement
    this.getStats().removeWithKey(elseStat.id);

    this.iftype = IfStatement.IFTYPE_IF;
    this.setElsestat(null);

    // remove the if head -> elseStat edge
    this.getFirst().removeSuccessor(this.getElseEdge());

    this.setElseEdge(null);

    if (this.getAllSuccessorEdges().isEmpty()) {
      StatEdge nextEdge = elseStat.getFirstSuccessor();

      nextEdge.changeSource(this);
      // No need to check the type, if the if didn't have any successors, the edge can't be a break edge with this
      // as the closure
    } else {
      ValidationHelper.validateTrue(
        this.getFirstSuccessor().getDestination() == elseStat.getFirstSuccessor().getDestination(),
        "Expected the empty elseStat of the if statement to have the same destination as the if statement");
      // no need to change the edge, just deleting the outgoing edge from the ifstat is enough
      elseStat.getFirstSuccessor().remove();
    }
  }

  public void fixIfInvariantEmptyIfBranch() {
    // if(){;}else{...} -> if(!){...}

    Statement ifStat = this.getIfstat();

    if (this.iftype != IfStatement.IFTYPE_IFELSE ||
      ifStat == null || // should be a different fix
      ifStat.type != StatementType.BASIC_BLOCK ||
      ifStat.getExprents() == null ||
      !ifStat.getExprents().isEmpty()) {
      return;
    }

    // move else to the if position
    this.getStats().removeWithKey(ifStat.id);

    this.iftype = IfStatement.IFTYPE_IF;
    this.setIfstat(this.getElsestat());
    this.setElsestat(null);
    this.rtfIfBodyIsFallThrough = !this.rtfIfBodyIsFallThrough; // bodies swapped

    // remove the if head -> ifStat edge
    this.getFirst().removeSuccessor(this.getIfEdge());

    this.setIfEdge(this.getElseEdge());
    this.setElseEdge(null);

    if (this.getAllSuccessorEdges().isEmpty()) {
      // Make the ifStat -> next edge point from the if statement to the next statement
      StatEdge nextEdge = ifStat.getFirstSuccessor();
      nextEdge.changeSource(this);
      // No need to check the type, if the if didn't have any successors, the edge can't be a break edge with this
      // as the closure
    } else {
      ValidationHelper.validateTrue(
        this.getFirstSuccessor().getDestination() == ifStat.getFirstSuccessor().getDestination(),
        "Expected the empty ifStat of the if statement to have the same destination as the if statement");
      // no need to change the edge, just deleting the outgoing edge from the ifstat is enough
      ifStat.getFirstSuccessor().remove();
    }

    // negate head expression
    this.setNegated(!this.isNegated());
    this.getHeadexprentList().set(0, ((IfExprent) this.getHeadexprent().copy()).negateIf());

    // RTF: track that this transformation flipped the condition direction
    if (DecompilerContext.isRoundtripFidelity()) {
      this.toggleRtfConditionFlipped();
    }
  }
}