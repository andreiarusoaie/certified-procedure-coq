package org.certprover.main;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterException;
import org.certprover.Prover;
import org.certprover.context.Context;
import org.certprover.options.CommandLineOptions;

import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Created by Andrei on 12/12/2014.
 *
 * The main class of the tool which gets the arguments and triggers the verification.
 */
public class Main {

    private static final Logger log = Logger.getLogger(Main.class.getName());

    public static void main(String[] args) {

        // parse command line options
        CommandLineOptions commandLineOptions = new CommandLineOptions();
        try {
            new JCommander(commandLineOptions, args);
        }
        catch (ParameterException pe) {
            log.log(Level.SEVERE, pe.getLocalizedMessage());
            // exit with non-zero code
            System.exit(1);
        }

        // create context object
        Context context = new Context(commandLineOptions);

        // launch the prover
        Prover prover = new Prover(context);
        prover.start();
   }
}
