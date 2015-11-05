package sat;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Scanner;

import immutable.EmptyImList;
import immutable.ImList;
import sat.env.Bool;
import sat.env.Environment;
import sat.env.Variable;
import sat.formula.Clause;
import sat.formula.Formula;
import sat.formula.Literal;
import sat.formula.NegLiteral;
import sat.formula.PosLiteral;

/**
 * A simple DPLL SAT solver. See http://en.wikipedia.org/wiki/DPLL_algorithm
 */
public class SATSolver {
    static boolean solvable = false;
    static Variable v = new Variable("solvable");

    public static Environment setLiteral(Literal l, Environment env) {
//        System.out.println("l is " + l.toString());
        if (l.getVariable().equals(l)) {
            env = env.putTrue(l.getVariable());
        } else {
            env = env.putFalse(l.getVariable());
        }
        return env;
    }
    /**
     * Solve the problem using a simple version of DPLL with backtracking and
     * unit propagation. The returned environment binds literals of class
     * bool.Variable rather than the special literals used in clausification of
     * class clausal.Literal, so that clients can more readily use it.
     * 
     * @return an environment for which the problem evaluates to Bool.TRUE, or
     *         null if no such environment exists.
     */
    public static Environment solve(Formula formula) {
//        System.out.println("Now at first Solve");
        Environment result = new Environment();
        ImList<Clause> clauses = formula.getClauses();
//        System.out.println("clauses = " + clauses.toString());


        if(formula.getSize()==0) { //check if input is null
            solvable = true;
            System.out.println("Solvable = " + solvable);
            result = result.put(v, Bool.TRUE);
        }

        else {
            Clause index = new Clause(); //for the smallest clause
            int smallest = 0;
            ImList<Clause> changed = new EmptyImList<>();
            for (Clause c : clauses) {
                if (c.isEmpty()) {
                    solvable = false;
//                    System.out.println("Solvable = " + solvable);
                    return result;
                }
                else {
                    if (smallest==0||c.size()<smallest) {
                        smallest = c.size();
                        index = c;
                    }
                }
            }
            if (index.isUnit()) { //check if index has only one literal
                Literal l = index.chooseLiteral();
//                System.out.println("l is " + l);
                changed = substitute(clauses, l);
                result = solve(changed, result);
                if(!result.getMap().isEmpty()) {
                    result = setLiteral(l, result);
                }
            } else{ //if more than 1 literal
                Literal l = index.chooseLiteral();
                changed = substitute(clauses, l);
                result = solve(changed, result);
                if(!result.getMap().isEmpty()) {
                    result = setLiteral(l, result);
                }
                else {
                    changed = substitute(clauses, l.getNegation());
                    result = solve(changed, result);
                    if(!result.getMap().isEmpty()) {
                        result = setLiteral(l.getNegation(),result);
                    }
                }
            }
        }

        if(!result.getMap().isEmpty()) {
            System.out.println("Satisfiable");
        }
        else {
            System.out.println("Unsatisfiable");
        }
        System.out.println(result.toString());
        return result;
    }

    /**
     * Takes a partial assignment of variables to values, and recursively
     * searches for a complete satisfying assignment.
     * 
     * @param clauses
     *            formula in conjunctive normal form
     * @param env
     *            assignment of some or all variables in clauses to true or
     *            false values.
     * @return an environment for which all the clauses evaluate to Bool.TRUE,
     *         or null if no such environment exists.
     */
    private static Environment solve(ImList<Clause> clauses, Environment env) {
//        System.out.println("Now using second solve type");
        Clause index = new Clause(); //for the smallest clause
//        System.out.println(clauses.toString());

        if(clauses.size()==0) {
            solvable = true;
//            System.out.println("Solvable = " + solvable);
            env = env.put(v,Bool.TRUE);
//            System.out.println(env.toString());
            return env;
        }
        else {
            int smallest = 0;
            ImList<Clause> changed = new EmptyImList<>();
            for (Clause c : clauses) {
                if (c.isEmpty()) {
                    solvable = false;
//                    System.out.println("Solvable = " + solvable);
                    return env;
                }
                else {
                    if (smallest==0||c.size()<smallest) {
                        smallest = c.size();
                        index = c;
                    }
                }
            }
            if (index.isUnit()) {
                Literal l = index.chooseLiteral();
//                System.out.println("l is " + l);
                changed = substitute(clauses, l);
                env = solve(changed, env);
                if(!env.getMap().isEmpty()) {
                    env = setLiteral(l, env);
                }
            } else{
                Literal l = index.chooseLiteral();
//                System.out.println("l is " + l);
                changed = substitute(clauses, l);
                env = solve(changed, env);
                if(!env.getMap().isEmpty()) {
                    env = setLiteral(l, env);
                }
                else {
                    changed = substitute(clauses, l.getNegation());
                    env = solve(changed, env);
                    if(!env.getMap().isEmpty()) {
                        env = setLiteral(l, env);
                    }


                }
            }


        }

        return env;
    }

    /**
     * given a clause list and literal, produce a new list resulting from
     * setting that literal to true
     * 
     * @param clauses
     *            , a list of clauses
     * @param l
     *            , a literal to set to true
     * @return a new list of clauses resulting from setting l to true
     */
    private static ImList<Clause> substitute(ImList<Clause> clauses,
            Literal l) {

        for(Clause c:clauses) {
            if (c.contains(l)) { //if clause contains l, remove the entire clause
                clauses = clauses.remove(c);
            }
            else if(c.contains(l.getNegation())) { //if clause contains the negation of l, remove negation of l
                clauses = clauses.remove(c);
                c = c.reduce(l);
                clauses = clauses.add(c);

            } //else, do nothing to the clause
        }
        return clauses;
    }

//    public static void main(String[] args) {
//        Literal a = PosLiteral.make("a");
//        Literal b = PosLiteral.make("b");
//        Literal c = PosLiteral.make("c");
//        Literal d = PosLiteral.make("d");
//        Literal e = PosLiteral.make("e");
//
//        Clause cA = new Clause(a);
//        Clause cB = new Clause(b);
//        Clause cC = new Clause(b.getNegation());
//        Clause cD = new Clause(c.getNegation());
//        Clause cE = new Clause(d.getNegation());
//        Clause cF = new Clause(d.getNegation());
//        Clause cG = new Clause(c.getNegation());
//        Clause cH = new Clause(d);
//
//        cA = cA.add(b);
//        cA = cA.add(e);
//        cB = cB.add(e);
//        cB = cB.add(c.getNegation());
//        cC = cC.add(c);
//        cD = cD.add(d);
//        cE = cE.add(b.getNegation());
//        cF = cF.add(c);
//        cG = cG.add(d.getNegation());
//        cH = cH.add(c);
//
//        Formula santa = new Formula();
//        santa = santa.addClause(cA);
//        santa = santa.addClause(cB);
//        santa = santa.addClause(cC);
//        santa = santa.addClause(cD);
//        santa = santa.addClause(cE);
//        santa = santa.addClause(cF);
//        santa = santa.addClause(cG);
//        santa = santa.addClause(cH);
//
////        solve(santa2);
//
//
//        solve(santa);
 public static void main(String[] args) throws IOException {
        InputStream is = null;
        int i=0;
        char c;
        String d="";
        String[] f={};
        boolean print=false;
        File file = new File("C:\\Users\\Hazel\\Desktop\\largeSat.cnf");

        Clause current = new Clause();
        Formula form = new Formula();

        try {

            Scanner sc = new Scanner(file);

            while (sc.hasNextLine()) {
                d = sc.nextLine();
                if (print) {
                    f=d.split(" ");
                    for (String g:f
                            ) {
                        if ((!g.equals("0"))&(!g.isEmpty())) {
                            if (g.substring(0,1).equals("-")) {
                                current = current.add(NegLiteral.make(g.substring(1)));
                            } else {
                                current = current.add(PosLiteral.make(g));
                            }
                        } else if (!g.isEmpty()) {
                            form = form.addClause(current);
                            current = new Clause();
                        }
                    }
                }
                if (d.startsWith("p")) {
                    print = true;
                }
            }
            sc.close();
        }
        catch (FileNotFoundException e) {
            e.printStackTrace();
        }
//        System.out.println(form);
        System.out.println("SAT solver starts!!!");
        long started = System.nanoTime();
        Environment e = SATSolver.solve(form);
        long time = System.nanoTime();
        long timeTaken= time - started;
        System.out.println("Time:" + timeTaken / 1000000.0 + "ms");
    }

}
