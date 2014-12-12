package org.certprover.main;

import com.beust.jcommander.JCommander;
import org.certprover.context.Context;
import org.certprover.options.CommandLineOptions;

/**
 * Created by Andrei on 12/12/2014.
 *
 * The main class of the tool which gets the arguments and triggers the verification.
 */
public class Main {
    public static void main(String[] args) {

        // parse command line options
        CommandLineOptions commandLineOptions = new CommandLineOptions();
        JCommander jCommander = new JCommander(commandLineOptions, args);

        // create context object
        Context context = new Context(commandLineOptions);
   }
}
