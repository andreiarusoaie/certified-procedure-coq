import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterException;
import org.certprover.context.Context;
import org.certprover.main.Main;
import org.certprover.options.CommandLineOptions;
import org.junit.Assert;
import org.junit.Test;

import java.io.File;
import java.util.logging.Level;

/**
 * Created by Andrei on 12/12/2014.
 */
public class ContextTest {
    @Test
    public void buildCorrectContextTest() {
        File def = new File("imp.k");
        File goals = new File("sum.k");

        String[] args = new String[] {"-d", def.getAbsolutePath(), "-g", goals.getAbsolutePath()};
        CommandLineOptions commandLineOptions = new CommandLineOptions();
        new JCommander(commandLineOptions, args);
        Context context = new Context(commandLineOptions);

        Assert.assertTrue(context.getDefinitionFileName().equals(def.getAbsolutePath()));
        Assert.assertTrue(context.getGoalsFileName().equals(goals.getAbsolutePath()));
    }
}
