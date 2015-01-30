package org.certprover;

import org.certprover.context.Context;
import org.certprover.utils.FileUtil;

/**
 * Created by Andrei on 12/12/2014.
 */
public class Prover {
    Context context;

    public Prover(Context context) {
        this.context = context;
    }

    public void start() {
        // compile the definition and the goals
        String compiledDefinition = kompile(context.getDefinitionFileName());
        String compiledGoals = kompile(context.getGoalsFileName());

        System.out.println(compiledDefinition);
        System.out.println(compiledGoals);
    }

    private String kompile(String file) {
        String compiledFile = FileUtil.stripExtension(file) + "-compiled";
        org.kframework.main.Main.main(new String[]{"-kompile", file, "-d", compiledFile});
        return compiledFile;
    }

    public boolean prove() {
        // procedure -> function
        return false;
    }
}
