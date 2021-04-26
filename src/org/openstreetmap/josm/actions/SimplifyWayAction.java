// License: GPL. For details, see LICENSE file.
package org.openstreetmap.josm.actions;

import static org.openstreetmap.josm.gui.help.HelpUtil.ht;
import static org.openstreetmap.josm.tools.I18n.tr;
import static org.openstreetmap.josm.tools.I18n.trn;

import java.awt.GridBagLayout;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.ForkJoinTask;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import javax.swing.BorderFactory;
import javax.swing.JCheckBox;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JSpinner;
import javax.swing.SpinnerNumberModel;
import javax.swing.SwingUtilities;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import org.openstreetmap.josm.command.ChangeNodesCommand;
import org.openstreetmap.josm.command.Command;
import org.openstreetmap.josm.command.DeleteCommand;
import org.openstreetmap.josm.command.SequenceCommand;
import org.openstreetmap.josm.data.SystemOfMeasurement;
import org.openstreetmap.josm.data.UndoRedoHandler;
import org.openstreetmap.josm.data.osm.DataSet;
import org.openstreetmap.josm.data.osm.Node;
import org.openstreetmap.josm.data.osm.OsmPrimitive;
import org.openstreetmap.josm.data.osm.Way;
import org.openstreetmap.josm.data.projection.Ellipsoid;
import org.openstreetmap.josm.gui.ExtendedDialog;
import org.openstreetmap.josm.gui.HelpAwareOptionPane;
import org.openstreetmap.josm.gui.HelpAwareOptionPane.ButtonSpec;
import org.openstreetmap.josm.gui.MainApplication;
import org.openstreetmap.josm.gui.Notification;
import org.openstreetmap.josm.gui.util.GuiHelper;
import org.openstreetmap.josm.spi.preferences.Config;
import org.openstreetmap.josm.spi.preferences.IPreferences;
import org.openstreetmap.josm.tools.GBC;
import org.openstreetmap.josm.tools.ImageProvider;
import org.openstreetmap.josm.tools.Logging;
import org.openstreetmap.josm.tools.Shortcut;
import org.openstreetmap.josm.tools.StreamUtils;

/**
 * Delete unnecessary nodes from a way
 * @since 2575
 */
public class SimplifyWayAction extends JosmAction {
    private static final int MAX_WAYS_NO_ASK = 10;

    /**
     * Constructs a new {@code SimplifyWayAction}.
     */
    public SimplifyWayAction() {
        super(tr("Simplify Way"), "simplify", tr("Delete unnecessary nodes from a way."),
                Shortcut.registerShortcut("tools:simplify", tr("Tools: {0}", tr("Simplify Way")), KeyEvent.VK_Y, Shortcut.SHIFT), true);
        setHelpId(ht("/Action/SimplifyWay"));
    }

    protected boolean confirmWayWithNodesOutsideBoundingBox(List<? extends OsmPrimitive> primitives) {
        return DeleteAction.checkAndConfirmOutlyingDelete(primitives, null);
    }

    protected void alertSelectAtLeastOneWay() {
        SwingUtilities.invokeLater(() ->
            new Notification(
                    tr("Please select at least one way to simplify."))
                    .setIcon(JOptionPane.WARNING_MESSAGE)
                    .setDuration(Notification.TIME_SHORT)
                    .setHelpTopic(ht("/Action/SimplifyWay#SelectAWayToSimplify"))
                    .show()
        );
    }

    protected boolean confirmSimplifyManyWays(int numWays) {
        ButtonSpec[] options = {
                new ButtonSpec(
                        tr("Yes"),
                        new ImageProvider("ok"),
                        tr("Simplify all selected ways"),
                        null),
                new ButtonSpec(
                        tr("Cancel"),
                        new ImageProvider("cancel"),
                        tr("Cancel operation"),
                        null)
        };
        return 0 == HelpAwareOptionPane.showOptionDialog(
                MainApplication.getMainFrame(),
                tr("The selection contains {0} ways. Are you sure you want to simplify them all?", numWays),
                tr("Simplify ways?"),
                JOptionPane.WARNING_MESSAGE,
                null, // no special icon
                options,
                options[0],
                ht("/Action/SimplifyWay#ConfirmSimplifyAll")
                );
    }

    /**
     * Asks the user for max-err value used to simplify ways, if not remembered before
     * @param text the text being shown
     * @param auto whether it's called automatically (conversion) or by the user
     * @return the max-err value or -1 if canceled
     * @since 15419
     */
    public static double askSimplifyWays(String text, boolean auto) {
        return askSimplifyWays(Collections.emptyList(), text, auto);
    }

    /**
     * Asks the user for max-err value used to simplify ways, if not remembered before. This is not asynchronous.
     * @param ways the ways that are being simplified (to show estimated number of nodes to be removed)
     * @param text the text being shown
     * @param auto whether it's called automatically (conversion) or by the user
     * @return the max-err value or -1 if canceled
     * @see #askSimplifyWays(Collection, String, boolean, SimplifyWayActionListener...)
     * @since 16566
     */
    public static double askSimplifyWays(List<Way> ways, String text, boolean auto) {
        AtomicReference<Double> returnVar = new AtomicReference<>((double) -1);
        AtomicBoolean hasRun = new AtomicBoolean();
        askSimplifyWays(ways, text, auto, (result, command) -> {
            synchronized (returnVar) {
                returnVar.set(result);
                returnVar.notifyAll();
                hasRun.set(true);
            }
        });
        if (!SwingUtilities.isEventDispatchThread()) {
            synchronized (returnVar) {
                while (!hasRun.get()) {
                    try {
                        // Wait 2 seconds
                        returnVar.wait(2000);
                    } catch (InterruptedException e) {
                        Logging.error(e);
                        Thread.currentThread().interrupt();
                    }
                }
            }
        }
        return returnVar.get();
    }

    /**
     * Asks the user for max-err value used to simplify ways, if not remembered before
     * @param waysCollection the ways that are being simplified (to show estimated number of nodes to be removed)
     * @param text the text being shown
     * @param auto whether it's called automatically (conversion) or by the user
     * @param listeners Listeners to call when the max error is calculated
     * @since xxx
     */
    public static void askSimplifyWays(Collection<Way> waysCollection, String text, boolean auto, SimplifyWayActionListener... listeners) {
        final Collection<SimplifyWayActionListener> realListeners = Stream.of(listeners).filter(Objects::nonNull).collect(Collectors.toList());
        final List<Way> ways;
        if (waysCollection instanceof List) {
            ways = (List<Way>) waysCollection;
        } else {
            ways = new ArrayList<>(waysCollection);
        }
        IPreferences s = Config.getPref();
        String key = "simplify-way." + (auto ? "auto." : "");
        String keyRemember = key + "remember";
        String keyError = key + "max-error";

        String r = s.get(keyRemember, "ask");
        if (auto && "no".equals(r)) {
            realListeners.forEach(listener -> listener.maxErrorListener(-1, null));
            return;
        } else if ("yes".equals(r)) {
            realListeners.forEach(listener -> listener.maxErrorListener(s.getDouble(keyError, 3.0), null));
            return;
        }

        JPanel p = new JPanel(new GridBagLayout());
        p.add(new JLabel("<html><body style=\"width: 375px;\">" + text + "<br><br>" +
                tr("This reduces unnecessary nodes along the way and is especially recommended if GPS tracks were recorded by time "
                 + "(e.g. one point per second) or when the accuracy was low (reduces \"zigzag\" tracks).")
                + "</body></html>"), GBC.eol());
        p.setBorder(BorderFactory.createEmptyBorder(5, 10, 10, 5));
        JPanel q = new JPanel(new GridBagLayout());
        q.add(new JLabel(tr("Maximum error (meters): ")));
        SpinnerNumberModel errorModel = new SpinnerNumberModel(
                s.getDouble(keyError, 3.0), 0.01, null, 0.5);
        JSpinner n = new JSpinner(errorModel);
        ((JSpinner.DefaultEditor) n.getEditor()).getTextField().setColumns(4);
        q.add(n);

        JLabel nodesToRemove = new JLabel();
        SimplifyChangeListener l = new SimplifyChangeListener(nodesToRemove, errorModel, ways);
        if (!ways.isEmpty()) {
            errorModel.addChangeListener(l);
            l.stateChanged(null);
            q.add(nodesToRemove, GBC.std().insets(5, 0, 0, 0));
            errorModel.getChangeListeners();
        }

        q.setBorder(BorderFactory.createEmptyBorder(14, 0, 10, 0));
        p.add(q, GBC.eol());
        JCheckBox c = new JCheckBox(tr("Do not ask again"));
        p.add(c, GBC.eol());

        ExtendedDialog ed = new ExtendedDialog(MainApplication.getMainFrame(),
                tr("Simplify way"), tr("Simplify"),
                auto ? tr("Proceed without simplifying") : tr("Cancel"))
                .setContent(p)
                .configureContextsensitiveHelp("Action/SimplifyWay", true);
        if (auto) {
            ed.setButtonIcons("simplify", "ok");
        } else {
            ed.setButtonIcons("ok", "cancel");
        }
        ed.addWindowListener(new WindowAdapter() {
            @Override
            public void windowClosed(WindowEvent e) {
                final double result;
                final int ret = ed.getValue();
                double val = (double) n.getValue();
                final Command command = l.lastCommand;
                if (l.lastCommand != null && l.lastCommand.equals(UndoRedoHandler.getInstance().getLastCommand())) {
                    UndoRedoHandler.getInstance().undo();
                    l.lastCommand = null;
                }
                if (ret == 1) {
                    s.putDouble(keyError, val);
                    if (c.isSelected()) {
                        s.put(keyRemember, "yes");
                    }
                    result = val;
                } else {
                    if (auto && c.isSelected()) { //do not remember cancel for manual simplify, otherwise nothing would happen
                        s.put(keyRemember, "no");
                    }
                    result = -1;
                }
                realListeners.forEach(listener -> listener.maxErrorListener(result, command));
            }
        });
        GuiHelper.runInEDT(ed::showDialog);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        DataSet ds = getLayerManager().getEditDataSet();
        List<Way> ways = ds.getSelectedWays().stream()
                .filter(p -> !p.isIncomplete())
                .collect(Collectors.toList());
        if (ways.isEmpty()) {
            alertSelectAtLeastOneWay();
            return;
        } else if (!confirmWayWithNodesOutsideBoundingBox(ways) || (ways.size() > MAX_WAYS_NO_ASK && !confirmSimplifyManyWays(ways.size()))) {
            return;
        }

        String lengthstr = SystemOfMeasurement.getSystemOfMeasurement().getDistText(
                ways.stream().mapToDouble(Way::getLength).sum());

        askSimplifyWays(ways, trn(
            "You are about to simplify {0} way with a total length of {1}.",
            "You are about to simplify {0} ways with a total length of {1}.",
            ways.size(), ways.size(), lengthstr), false, (maxErr, simplifyCommand) -> {
                if (maxErr > 0) {
                    if (simplifyCommand == null) {
                        simplifyWays(ways, maxErr);
                    } else {
                        GuiHelper.runInEDT(() -> UndoRedoHandler.getInstance().add(simplifyCommand));
                    }
                }
            }
        );

    }

    /**
     * Replies true if <code>node</code> is a required node which can't be removed
     * in order to simplify the way.
     *
     * @param way the way to be simplified
     * @param node the node to check
     * @param multipleUseNodes set of nodes which is used more than once in the way
     * @return true if <code>node</code> is a required node which can't be removed
     * in order to simplify the way.
     */
    protected static boolean isRequiredNode(Way way, Node node, Set<Node> multipleUseNodes) {
        boolean isRequired = node.isTagged();
        if (!isRequired && multipleUseNodes.contains(node)) {
            int frequency = Collections.frequency(way.getNodes(), node);
            if ((way.getNode(0) == node) && (way.getNode(way.getNodesCount()-1) == node)) {
                frequency = frequency - 1; // closed way closing node counted only once
            }
            isRequired = frequency > 1;
        }
        if (!isRequired) {
            List<OsmPrimitive> parents = new LinkedList<>();
            parents.addAll(node.getReferrers());
            parents.remove(way);
            isRequired = !parents.isEmpty();
        }
        return isRequired;
    }

    /**
     * Calculate a set of nodes which occurs more than once in the way
     * @param w the way
     * @return a set of nodes which occurs more than once in the way
     */
    private static Set<Node> getMultiUseNodes(Way w) {
        Set<Node> allNodes = new HashSet<>();
        return w.getNodes().stream()
                .filter(n -> !allNodes.add(n))
                .collect(Collectors.toSet());
    }

    /**
     * Runs the commands to simplify the ways with the given threshold
     *
     * @param ways the ways to simplify
     * @param threshold the max error threshold
     * @return The number of nodes removed from the ways (does not double-count)
     * @since 16566
     */
    public static int simplifyWaysCountNodesRemoved(List<Way> ways, double threshold) {
        Command command = buildSimplifyWaysCommand(ways, threshold);
        if (command == null) {
            return 0;
        }
        return (int) command.getParticipatingPrimitives().stream()
                .filter(Node.class::isInstance)
                .count();
    }

    /**
     * Runs the commands to simplify the ways with the given threshold
     *
     * @param ways the ways to simplify
     * @param threshold the max error threshold
     * @since 15419
     */
    public static void simplifyWays(List<Way> ways, double threshold) {
        Command command = buildSimplifyWaysCommand(ways, threshold);
        if (command != null) {
            UndoRedoHandler.getInstance().add(command);
        }
    }

    /**
     * Creates the commands to simplify the ways with the given threshold
     *
     * @param ways the ways to simplify
     * @param threshold the max error threshold
     * @return The command to simplify ways
     * @since 16566 (private)
     */
    private static SequenceCommand buildSimplifyWaysCommand(List<Way> ways, double threshold) {
        // Use `parallelStream` since this can significantly decrease the amount of time taken for large numbers of ways
        Collection<Command> allCommands = ways.parallelStream()
                .map(way -> createSimplifyCommand(way, threshold))
                .filter(Objects::nonNull)
                .collect(StreamUtils.toUnmodifiableList());
        if (allCommands.isEmpty())
            return null;
        return new SequenceCommand(
                trn("Simplify {0} way", "Simplify {0} ways", allCommands.size(), allCommands.size()),
                allCommands);
    }

    /**
     * Creates the SequenceCommand to simplify a way with default threshold.
     *
     * @param w the way to simplify
     * @return The sequence of commands to run
     * @since 15419
     */
    public static SequenceCommand createSimplifyCommand(Way w) {
        return createSimplifyCommand(w, Config.getPref().getDouble("simplify-way.max-error", 3.0));
    }

    /**
     * Creates the SequenceCommand to simplify a way with a given threshold.
     *
     * @param w the way to simplify
     * @param threshold the max error threshold
     * @return The sequence of commands to run
     * @since 15419
     */
    public static SequenceCommand createSimplifyCommand(Way w, double threshold) {
        int lower = 0;
        int i = 0;

        Set<Node> multipleUseNodes = getMultiUseNodes(w);
        List<Node> newNodes = new ArrayList<>(w.getNodesCount());
        while (i < w.getNodesCount()) {
            if (isRequiredNode(w, w.getNode(i), multipleUseNodes)) {
                // copy a required node to the list of new nodes. Simplify not possible
                newNodes.add(w.getNode(i));
                i++;
                lower++;
                continue;
            }
            i++;
            // find the longest sequence of not required nodes ...
            while (i < w.getNodesCount() && !isRequiredNode(w, w.getNode(i), multipleUseNodes)) {
                i++;
            }
            // ... and simplify them
            buildSimplifiedNodeList(w.getNodes(), lower, Math.min(w.getNodesCount()-1, i), threshold, newNodes);
            lower = i;
            i++;
        }

        // Closed way, check if the first node could also be simplified ...
        if (newNodes.size() > 3 && newNodes.get(0) == newNodes.get(newNodes.size() - 1)
                && !isRequiredNode(w, newNodes.get(0), multipleUseNodes)) {
            final List<Node> l1 = Arrays.asList(newNodes.get(newNodes.size() - 2), newNodes.get(0), newNodes.get(1));
            final List<Node> l2 = new ArrayList<>(3);
            buildSimplifiedNodeList(l1, 0, 2, threshold, l2);
            if (!l2.contains(newNodes.get(0))) {
                newNodes.remove(0);
                newNodes.set(newNodes.size() - 1, newNodes.get(0)); // close the way
            }
        }

        if (newNodes.size() == w.getNodesCount()) return null;

        Set<Node> delNodes = new HashSet<>(w.getNodes());
        delNodes.removeAll(newNodes);

        if (delNodes.isEmpty()) return null;

        Collection<Command> cmds = new LinkedList<>();
        cmds.add(new ChangeNodesCommand(w, newNodes));
        cmds.add(new DeleteCommand(w.getDataSet(), delNodes));
        w.getDataSet().clearSelection(delNodes);
        return new SequenceCommand(
                trn("Simplify Way (remove {0} node)", "Simplify Way (remove {0} nodes)", delNodes.size(), delNodes.size()), cmds);
    }

    /**
     * Builds the simplified list of nodes for a way segment given by a lower index <code>from</code>
     * and an upper index <code>to</code>
     *
     * @param wnew the way to simplify
     * @param from the lower index
     * @param to the upper index
     * @param threshold the max error threshold
     * @param simplifiedNodes list that will contain resulting nodes
     */
    protected static void buildSimplifiedNodeList(List<Node> wnew, int from, int to, double threshold, List<Node> simplifiedNodes) {

        Node fromN = wnew.get(from);
        Node toN = wnew.get(to);

        // Get max xte
        int imax = -1;
        double xtemax = 0;
        for (int i = from + 1; i < to; i++) {
            Node n = wnew.get(i);
            // CHECKSTYLE.OFF: SingleSpaceSeparator
            double xte = Math.abs(Ellipsoid.WGS84.a
                    * xtd(fromN.lat() * Math.PI / 180, fromN.lon() * Math.PI / 180, toN.lat() * Math.PI / 180,
                            toN.lon() * Math.PI / 180,     n.lat() * Math.PI / 180,   n.lon() * Math.PI / 180));
            // CHECKSTYLE.ON: SingleSpaceSeparator
            if (xte > xtemax) {
                xtemax = xte;
                imax = i;
            }
        }

        if (imax != -1 && xtemax >= threshold) {
            // Segment cannot be simplified - try shorter segments
            buildSimplifiedNodeList(wnew, from, imax, threshold, simplifiedNodes);
            buildSimplifiedNodeList(wnew, imax, to, threshold, simplifiedNodes);
        } else {
            // Simplify segment
            if (simplifiedNodes.isEmpty() || simplifiedNodes.get(simplifiedNodes.size()-1) != fromN) {
                simplifiedNodes.add(fromN);
            }
            if (fromN != toN) {
                simplifiedNodes.add(toN);
            }
        }
    }

    /* From Aviaton Formulary v1.3
     * http://williams.best.vwh.net/avform.htm
     */
    private static double dist(double lat1, double lon1, double lat2, double lon2) {
        return 2 * Math.asin(Math.sqrt(Math.pow(Math.sin((lat1 - lat2) / 2), 2) + Math.cos(lat1) * Math.cos(lat2)
                * Math.pow(Math.sin((lon1 - lon2) / 2), 2)));
    }

    private static double course(double lat1, double lon1, double lat2, double lon2) {
        return Math.atan2(Math.sin(lon1 - lon2) * Math.cos(lat2), Math.cos(lat1) * Math.sin(lat2) - Math.sin(lat1)
                * Math.cos(lat2) * Math.cos(lon1 - lon2))
                % (2 * Math.PI);
    }

    private static double xtd(double lat1, double lon1, double lat2, double lon2, double lat3, double lon3) {
        double distAD = dist(lat1, lon1, lat3, lon3);
        double crsAD = course(lat1, lon1, lat3, lon3);
        double crsAB = course(lat1, lon1, lat2, lon2);
        return Math.asin(Math.sin(distAD) * Math.sin(crsAD - crsAB));
    }

    @Override
    protected void updateEnabledState() {
        updateEnabledStateOnCurrentSelection();
    }

    @Override
    protected void updateEnabledState(Collection<? extends OsmPrimitive> selection) {
        updateEnabledStateOnModifiableSelection(selection);
    }

    private static class SimplifyChangeListener implements ChangeListener {
        Command lastCommand;
        private final JLabel nodesToRemove;
        private final SpinnerNumberModel errorModel;
        private final List<Way> ways;
        private ForkJoinTask<?> futureNodesToRemove;

        SimplifyChangeListener(JLabel nodesToRemove, SpinnerNumberModel errorModel, List<Way> ways) {
            this.nodesToRemove = nodesToRemove;
            this.errorModel = errorModel;
            this.ways = ways;
        }

        @Override
        public void stateChanged(ChangeEvent e) {
            MainApplication.worker.execute(() -> {
                synchronized (errorModel) {
                    double threshold = errorModel.getNumber().doubleValue();
                    if (futureNodesToRemove != null) {
                        futureNodesToRemove.cancel(false);
                    }
                    futureNodesToRemove = MainApplication.getForkJoinPool().submit(new ForkJoinTask<Command>() {
                        private Command result;

                        @Override
                        public Command getRawResult() {
                            return result;
                        }

                        @Override
                        protected void setRawResult(Command value) {
                            this.result = value;
                        }

                        @Override
                        protected boolean exec() {
                            synchronized (SimplifyChangeListener.this) {
                                if (!this.isCancelled()) {
                                    GuiHelper.runInEDT(() -> nodesToRemove.setText(tr("calculating...")));
                                    result = updateNodesToRemove(ways, threshold);
                                    return true;
                                }
                            }
                            return false;
                        }
                    });
                }
            });
        }

        private Command updateNodesToRemove(List<Way> ways, double threshold) {
            // This must come first in order for everything else to be accurate
            if (lastCommand != null && lastCommand.equals(UndoRedoHandler.getInstance().getLastCommand())) {
                // We need to wait to avoid cases where we cannot undo due threading issues.
                GuiHelper.runInEDTAndWait(() -> UndoRedoHandler.getInstance().undo());
            }
            final Command command = buildSimplifyWaysCommand(ways, threshold);
            // This is the same code from simplifyWaysCountNodesRemoved, but is duplicated for performance reasons
            // (this avoids running the code to calculate the command twice).
            int removeNodes = command == null ? 0 : (int) command.getParticipatingPrimitives().stream()
                    .filter(Node.class::isInstance)
                    .count();
            int totalNodes = ways.parallelStream().mapToInt(Way::getNodesCount).sum();
            int percent = (int) Math.round(100 * removeNodes / (double) totalNodes);
            GuiHelper.runInEDTAndWait(() ->
                    nodesToRemove.setText(trn(
                            "(about {0} node to remove ({1}%))",
                            "(about {0} nodes to remove ({1}%))", removeNodes, removeNodes, percent))
            );
            lastCommand = command;
            if (lastCommand != null && ways.size() < MAX_WAYS_NO_ASK) {
                GuiHelper.runInEDTAndWait(() -> UndoRedoHandler.getInstance().add(lastCommand));
            }
            return lastCommand;
        }
    }


    /**
     * A listener that is called when the {@link #askSimplifyWays} method is called.
     * @since xxx
     */
    @FunctionalInterface
    public interface SimplifyWayActionListener {
        /**
         * Called when the max error is set
         * @param maxError The max error
         * @param simplify The command that was used to generate stats for the user with the maxError. May be null.
         */
        void maxErrorListener(double maxError, Command simplify);
    }
}
