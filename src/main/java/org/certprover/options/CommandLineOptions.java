package org.certprover.options;

import com.beust.jcommander.Parameter;

/**
 * Created by Andrei on 12/12/2014.
 *
 * Command line options of the tool.
 */
public class CommandLineOptions {
    @Parameter(names = { "-d", "--definition" }, description = "The K definition of the language", required = true)
    private String definition;

    @Parameter(names = { "-g", "--goals" }, description = "The goals to be proved", required = true)
    private String goals;

    @Parameter(names = { "-dom", "--domain" }, description = "The data domain file")
    private String domain;

    @Parameter(names = { "-v", "--verbose" }, description = "Verbose mode")
    private boolean verbose;

    @Parameter(names = { "-h", "--help" }, description = "Display this message", help = true)
    private boolean help;

    public CommandLineOptions() {
    }

    public String getDefinition() {
        return definition;
    }

    public String getGoals() {
        return goals;
    }

    public String getDomain() {
        return domain;
    }

    public boolean isVerbose() {
        return verbose;
    }

    public boolean isHelp() {
        return help;
    }
}
