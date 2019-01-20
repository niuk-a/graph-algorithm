package org.niuka.soc.leuven;

import java.util.Arrays;
import java.util.BitSet;
import java.util.Date;
import java.util.concurrent.ThreadLocalRandom;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Leuven {

    private static Graph karate_club() {
        // https://en.wikipedia.org/wiki/Zachary%27s_karate_club
        String data = "" +
                "[2 1]\n" +
                "[3 1] [3 2]\n" +
                "[4 1] [4 2] [4 3]\n" +
                "[5 1]\n" +
                "[6 1]\n" +
                "[7 1] [7 5] [7 6]\n" +
                "[8 1] [8 2] [8 3] [8 4]\n" +
                "[9 1] [9 3]\n" +
                "[10 3]\n" +
                "[11 1] [11 5] [11 6]\n" +
                "[12 1]\n" +
                "[13 1] [13 4]\n" +
                "[14 1] [14 2] [14 3] [14 4]\n" +
                "[17 6] [17 7]\n" +
                "[18 1] [18 2]\n" +
                "[20 1] [20 2]\n" +
                "[22 1] [22 2]\n" +
                "[26 24] [26 25]\n" +
                "[28 3] [28 24] [28 25]\n" +
                "[29 3]\n" +
                "[30 24] [30 27]\n" +
                "[31 2] [31 9]\n" +
                "[32 1] [32 25] [32 26] [32 29]\n" +
                "[33 3] [33 9] [33 15] [33 16] [33 19] [33 21] [33 23] [33 24] [33 30] [33 31] [33 32]\n" +
                "[34 9] [34 10] [34 14] [34 15] [34 16] [34 19] [34 20] [34 21] [34 23] [34 24] [34 27] [34 28] [34 29] [34 30] [34 31] [34 32] [34 33]";
        Graph graph = new Graph(34, 156, false);
        Pattern pattern = Pattern.compile("\\[([0-9]{1,2}) ([0-9]{1,2})]([ |\n])");
        Matcher matcher = pattern.matcher(data);
        while (matcher.find()) {
            int s = Integer.parseInt(matcher.group(1)) - 1;
            int t = Integer.parseInt(matcher.group(2)) - 1;
            graph.degrees[s]++;
            graph.degrees[t]++;
        }
        for (int i = 1; i < graph.degrees.length; i++) {
            graph.degrees[i] += graph.degrees[i - 1];
        }
        int[] pos = new int[graph.degrees.length];
        matcher = pattern.matcher(data);
        while (matcher.find()) {
            int s = Integer.parseInt(matcher.group(1)) - 1;
            int t = Integer.parseInt(matcher.group(2)) - 1;
            graph.links[(s == 0 ? 0 : graph.degrees[s - 1]) + pos[s]++] = t;
            graph.links[(t == 0 ? 0 : graph.degrees[t - 1]) + pos[t]++] = s;
        }
        for (int n = 0; n < graph.degrees.length; n++) {
            graph.total_weight += graph.weighted_degree(n);
        }
        return graph;
    }

    public static void main(String[] argv) {
        int precision = Integer.getInteger("precision");

        Graph g = karate_club();
        Community c = new Community(g, -1, precision);
        boolean improvement;
        do {
            improvement = c.one_level();
            double new_mod = c.modularity();
            System.out.println(new Date() + " " + new_mod);
            g = c.partition2graph_binary();
            c = new Community(g, -1, precision);
        } while (improvement);
    }

    static class Graph {
        final int[] degrees;
        final int[] links;
        final float[] weights;
        double total_weight;

        Graph(int nodeCount, int linkCount, boolean weight) {
            this.degrees = new int[nodeCount];
            this.links = new int[linkCount];
            this.weights = weight ? new float[linkCount] : null;
        }


        // return the number of neighbors (degree) of the node
        int nb_neighbors(int node) {
            assert node >= 0 && node < degrees.length;
            return node == 0 ? degrees[0] : degrees[node] - degrees[node - 1];
        }

        // return the number of self loops of the node
        double nb_selfloops(int node) {
            assert node >= 0 && node < degrees.length;
            for (int i = 0, p = neighbors(node); i < nb_neighbors(node); i++, p++) {
                if (links[p] == node) {
                    return weights == null ? 1. : weights[p];
                }
            }
            return 0.;
        }

        // return the weighted degree of the node
        double weighted_degree(int node) {
            assert node >= 0 && node < degrees.length;
            if (weights == null) {
                return nb_neighbors(node);
            }
            double res = 0;
            for (int p = neighbors(node), i = 0; i < nb_neighbors(node); i++, p++) {
                res += weights[p];
            }
            return res;
        }

        // return pointers to the first neighbor and first weight of the node
        int neighbors(int node) {
            assert node >= 0 && node < degrees.length;
            assert weights != null;
            return node == 0 ? 0 : degrees[node - 1];
        }
    }

    static class Community {
        final double[] neigh_weight;
        final int[] neigh_pos;
        int neigh_last;

        final Graph g; // network to compute communities for
        final int[] n2c; // community to which each node belongs
        final double[] in, tot; // used to compute the modularity participation of each community

        // number of pass for one level computation
        // if -1, compute as many pass as needed to increase modularity
        final int nb_pass;

        // a new pass is computed if the last one has generated an increase
        // greater than min_modularity
        // if 0. even a minor increase is enough to go for one more pass
        final double min_modularity;

        // copy graph
        Community(Graph g, int nb_pass, double min_modularity) {
            this.g = g;

            this.neigh_weight = new double[g.degrees.length];
            Arrays.fill(neigh_weight, -1);
            this.neigh_pos = new int[g.degrees.length];
            this.neigh_last = 0;

            this.n2c = new int[g.degrees.length];
            this.in = new double[g.degrees.length];
            this.tot = new double[g.degrees.length];

            for (int i = 0; i < g.degrees.length; i++) {
                this.n2c[i] = i;
                this.in[i] = g.nb_selfloops(i);
                this.tot[i] = g.weighted_degree(i);
            }

            this.nb_pass = nb_pass;
            this.min_modularity = min_modularity;
        }

        // compute the set of neighboring communities of node
        // for each community, gives the number of links from node to comm
        void neigh_comm(int node) {
            for (int i = 0; i < neigh_last; i++) {
                neigh_weight[neigh_pos[i]] = -1;
            }
            neigh_last = 0;

            int p = g.neighbors(node);
            long deg = g.nb_neighbors(node);

            neigh_pos[0] = n2c[node];
            neigh_weight[neigh_pos[0]] = 0;
            neigh_last = 1;

            for (int i = 0; i < deg; i++) {
                int neigh = g.links[p + i];
                int neigh_comm = n2c[neigh];
                double neigh_w = g.weights == null ? 1. : g.weights[p + i];

                if (neigh != node) {
                    if (neigh_weight[neigh_comm] == -1) {
                        neigh_weight[neigh_comm] = 0.;
                        neigh_pos[neigh_last++] = neigh_comm;
                    }
                    neigh_weight[neigh_comm] += neigh_w;
                }
            }
        }

        // compute the modularity of the current partition
        double modularity() {
            double q = 0.;
            for (int i = 0; i < g.degrees.length; i++) {
                if (tot[i] > 0) {
                    q += in[i] / g.total_weight - (tot[i] / g.total_weight) * (tot[i] / g.total_weight);
                }
            }
            return q;
        }

        // displays the graph of communities as computed by one_level
        void partition2graph() {
            int[] renumber = new int[g.degrees.length];
            Arrays.fill(renumber, -1);
            for (int node = 0; node < g.degrees.length; node++) {
                renumber[n2c[node]]++;
            }
            int final0 = 0;
            for (int i = 0; i < g.degrees.length; i++) {
                if (renumber[i] != -1) {
                    renumber[i] = final0++;
                }
            }
            for (int i = 0; i < g.degrees.length; i++) {
                for (int j = 0, p = g.neighbors(i); j < g.nb_neighbors(i); j++, p++) {
                    System.out.append(Integer.toString(renumber[n2c[i]])).append(' ')
                            .append(Integer.toString(renumber[n2c[g.links[p]]])).append('\n');
                }
            }
        }

        // displays the current partition (with communities renumbered from 0 to k-1)
        void display_partition() {
            int[] renumber = new int[g.degrees.length];
            Arrays.fill(renumber, -1);
            for (int node = 0; node < g.degrees.length; node++) {
                renumber[n2c[node]]++;
            }

            int final0 = 0;
            for (int i = 0; i < g.degrees.length; i++) {
                if (renumber[i] != -1) {
                    renumber[i] = final0++;
                }
            }

            for (int i = 0; i < g.degrees.length; i++) {
                System.out.append(Integer.toString(i)).append(' ')
                        .append(Integer.toString(renumber[n2c[i]])).append('\n');
            }
        }

        // generates the binary graph of communities as computed by one_level
        Graph partition2graph_binary() {
            // Renumber communities
            int[] renumber = new int[g.degrees.length];
            Arrays.fill(renumber, -1);
            for (int node = 0; node < g.degrees.length; node++) {
                renumber[n2c[node]]++;
            }

            int final0 = 0;
            for (int i = 0; i < g.degrees.length; i++) {
                if (renumber[i] != -1) {
                    renumber[i] = final0++;
                }
            }

            // Compute communities
            int[][] comm_nodes = new int[final0][];
            for (int node = 0; node < g.degrees.length; node++) {
                comm_nodes[renumber[n2c[node]]].push_back(node);
            }

            // Compute weighted graph
            int nb_links = 0;
            Graph g2 = new Graph(final0, );

            float[] m = new float[final0];
            BitSet m_fill = new BitSet(m.length);
            int link_count = 0;

            for (int comm = 0; comm < final0; comm++) {
                Arrays.fill(m, 0);
                m_fill.clear();
                int comm_size = comm_nodes[comm].size();
                for (int node = 0; node < comm_size; node++) {
                    int p = g.neighbors(comm_nodes[comm][node]);
                    int deg = g.nb_neighbors(comm_nodes[comm][node]);
                    for (int i = 0; i < deg; i++) {
                        int neigh = g.links[p + i];
                        int neigh_comm = renumber[n2c[neigh]];
                        double neigh_weight = (g.weights == null) ? 1. : g.weights[p + i];
                        m_fill.set(neigh_comm);
                        m[neigh_comm] += neigh_weight;
                    }
                }
                g2.degrees[comm] = (comm == 0 ? 0 : g2.degrees[comm - 1]) + m_fill.cardinality();
                nb_links += m_fill.cardinality();

                for (int i = m_fill.nextSetBit(0); i >= 0; i = m_fill.nextSetBit(i + 1)) {
                    g2.total_weight += m[i];
                    g2.links[link_count] = i;
                    g2.weights[link_count] = m[i];
                    link_count++;
                }
            }

            return g2;
        }

        // compute communities of the graph for one level
        // return true if some nodes have been moved
        boolean one_level() {
            boolean improvement = false;
            int nb_moves;
            double new_mod = modularity();
            double cur_mod;

            int[] random_order = new int[g.degrees.length];
            for (int i = 0; i < g.degrees.length; i++) {
                random_order[i] = i;
            }
            for (int i = 0; i < g.degrees.length - 1; i++) {
                int rand_pos = ThreadLocalRandom.current().nextInt() % (g.degrees.length - i) + i;
                int tmp = random_order[i];
                random_order[i] = random_order[rand_pos];
                random_order[rand_pos] = tmp;
            }

            // repeat while
            //   there is an improvement of modularity
            //   or there is an improvement of modularity greater than a given epsilon
            //   or a predefined number of pass have been done
            do {
                cur_mod = new_mod;
                nb_moves = 0;
                // for each node: remove the node from its community and insert it in the best community
                for (int node_tmp = 0; node_tmp < g.degrees.length; node_tmp++) {
                    int node = random_order[node_tmp];
                    int node_comm = n2c[node];
                    double w_degree = g.weighted_degree(node);

                    // computation of all neighboring communities of current node
                    neigh_comm(node);
                    // remove node from its current community
                    tot[node_comm] -= g.weighted_degree(node);
                    in[node_comm] -= 2 * neigh_weight[node_comm] + g.nb_selfloops(node);
                    n2c[node] = -1;

                    // compute the nearest community for node
                    // default choice for future insertion is the former community
                    int best_comm = node_comm;
                    double best_nblinks = 0.;
                    double best_increase = 0.;
                    for (int i = 0; i < neigh_last; i++) {
                        // compute the gain of modularity if node where inserted in comm
                        // given that node has dnodecomm links to comm.  The formula is:
                        // [(In(comm)+2d(node,comm))/2m - ((tot(comm)+deg(node))/2m)^2]-
                        // [In(comm)/2m - (tot(comm)/2m)^2 - (deg(node)/2m)^2]
                        // where In(comm)    = number of half-links strictly inside comm
                        //       Tot(comm)   = number of half-links inside or outside comm (sum(degrees))
                        //       d(node,com) = number of links from node to comm
                        //       deg(node)   = node degree
                        //       m           = number of links
                        double increase = (neigh_weight[neigh_pos[i]] - tot[neigh_pos[i]] * w_degree / g.total_weight);
                        if (increase > best_increase) {
                            best_comm = neigh_pos[i];
                            best_nblinks = neigh_weight[neigh_pos[i]];
                            best_increase = increase;
                        }
                    }

                    // insert node in the nearest community
                    tot[best_comm] += g.weighted_degree(node);
                    in[best_comm] += 2 * best_nblinks + g.nb_selfloops(node);
                    n2c[node] = best_comm;

                    if (best_comm != node_comm) {
                        nb_moves++;
                    }
                }
                if (nb_moves > 0) {
                    improvement = true;
                }
                new_mod = modularity();
            } while (nb_moves > 0 && new_mod - cur_mod > min_modularity);

            return improvement;
        }
    }
}
