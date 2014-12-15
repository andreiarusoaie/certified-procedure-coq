import org.certprover.utils.FileUtil;
import org.junit.Test;

/**
 * Created by pastrav on 15/12/14.
 */
public class FileUtilTests {

    @Test
    public void stripExtensionTest(){
        String filename1 = "imp.k";
        String filename2 = "/some/home/path/and/imp.k";

        org.junit.Assert.assertTrue(FileUtil.stripExtension(filename1).equals("imp"));
        org.junit.Assert.assertTrue(FileUtil.stripExtension(filename2).equals("imp"));
    }
}
