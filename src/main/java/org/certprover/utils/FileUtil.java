package org.certprover.utils;

import java.io.File;
import java.io.FileNotFoundException;

/**
 * Created by Andrei on 12/12/2014.
 *
 * File custom utility functions.
 */
public class FileUtil {
    public static String getAbsolutePath(String file) {
        return file == null ? null : new File(file).getAbsolutePath();
    }
}
