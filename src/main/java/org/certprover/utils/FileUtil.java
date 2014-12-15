package org.certprover.utils;

import java.io.File;
import java.io.FileNotFoundException;

/**
 * Created by Andrei on 12/12/2014.
 *
 * Customized utility functions.
 */
public class FileUtil {
    /**
     * Compute the absolute file path.
     * @param filename is the name of an *existing* file
     * If filename does not exist, then the result is not guaranteed to be correct.
     * If the filename is null, then the result is null.
     * @return the absolute file path
     */
    public static String getAbsolutePath(String filename) {
        return filename == null ? null : new File(filename).getAbsolutePath();
    }

    /**
     * Strip extension from file name.
     * @param filename the file name or its absolute path
     * @return the file name without extension
     */
    public static String stripExtension(String filename) {
        return filename == null ? null : new File(filename).getName().replaceAll("\\..*", "");
    }
}
