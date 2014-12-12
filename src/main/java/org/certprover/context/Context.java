package org.certprover.context;

/**
 * Created by Andrei on 12/12/2014.
 * <p/>
 * This class contains all the needed parameters such that the whole tool
 * is functional.
 */
public class Context {

    private String definitionFileName;
    private String goalsFileName;
    private String dataDomainFile;

    public Context(String definitionFileName, String goalsFileName, String dataDomainFile) {
        this.definitionFileName = definitionFileName;
        this.goalsFileName = goalsFileName;
        this.dataDomainFile = dataDomainFile;
    }
}
