// License: GPL. For details, see LICENSE file.
package org.openstreetmap.josm.gui.layer.geoimage;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.openstreetmap.josm.testutils.annotations.BasicPreferences;
import org.openstreetmap.josm.tools.StreamUtils;

import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Unit tests of {@link ThumbsLoader} class.
 */
@BasicPreferences
class ThumbsLoaderTest {
    /**
     * Performance test for {@link ThumbsLoader}
     * @throws Exception if any error occurs
     */
    @Test
    @Disabled("Set working directory to image folder and run manually")
    void testPerformance() throws Exception {
        List<ImageEntry> imageEntries;
        try (DirectoryStream<Path> stream = Files.newDirectoryStream(Paths.get(".").toAbsolutePath(), "*.{JPG,jpg}")) {
            imageEntries = StreamUtils.toStream(stream).map(Path::toFile).map(ImageEntry::new).collect(Collectors.toList());
        }
        new ThumbsLoader(imageEntries).run();
        for (ImageEntry imageEntry : imageEntries) {
            assertNotNull(imageEntry.getThumbnail());
            assertEquals(ThumbsLoader.maxSize, Math.max(
                    imageEntry.getThumbnail().getWidth(null),
                    imageEntry.getThumbnail().getHeight(null)));
        }
    }

}
