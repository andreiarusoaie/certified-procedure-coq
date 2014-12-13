package org.certprover.options;

import com.beust.jcommander.IParameterValidator;
import com.beust.jcommander.ParameterException;

import java.io.File;

/**
 * Created by Andrei on 12/13/2014.
 */
public class FileArgumentValidator implements IParameterValidator {
    @Override
    public void validate(String name, String value) throws ParameterException {
        if (!new File(value).exists()) {
            throw new ParameterException("File " + value + " does not exist. Command line option " + name + " is provided with bad argument.");
        }
    }
}
