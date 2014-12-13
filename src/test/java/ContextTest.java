import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterException;
import org.certprover.context.Context;
import org.certprover.main.Main;
import org.certprover.options.CommandLineOptions;
import org.junit.Assert;
import org.junit.Test;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.util.logging.Level;

/**
 * Created by Andrei on 12/12/2014.
 */
public class ContextTest {
    @Test
    public void buildCorrectContextTest() {
        String DEF = "def.k";
        String GOALS = "goals.k";

        // create files
        try {
            PrintWriter defWriter = new PrintWriter(DEF, "UTF-8");
            defWriter.close();
            PrintWriter goalsWriter = new PrintWriter(GOALS, "UTF-8");
            goalsWriter.close();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (UnsupportedEncodingException e) {
            e.printStackTrace();
        }

        // parse command line arguments with given existing files
        String[] args = new String[] {"-d", DEF, "-g", GOALS};
        CommandLineOptions commandLineOptions = new CommandLineOptions();
        new JCommander(commandLineOptions, args);
        Context context = new Context(commandLineOptions);

        // delete files
        new File(DEF).delete();
        new File(GOALS).delete();

        // final assertions
        Assert.assertTrue(context.getDefinitionFileName().equals(new File(DEF).getAbsolutePath()));
        Assert.assertTrue(context.getGoalsFileName().equals(new File(GOALS).getAbsolutePath()));
    }
}
