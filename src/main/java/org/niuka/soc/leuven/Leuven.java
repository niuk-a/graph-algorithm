package org.niuka.soc.leuven;

import java.util.Arrays;
import java.util.concurrent.ThreadLocalRandom;

public class Leuven {

    public static void main(String[] argv) {
        String input = System.getProperty("input");
        String input_w = System.getProperty("input.w");
        String partitions = System.getProperty("partitions");
        int precision = Integer.getInteger("precision");

        Graph g = new Graph(input, input_w);
        Community c = new Community(g, -1, precision);
        if (partitions != null) {
            c.init_partition(partitions);
        }
        boolean improvement;
        do {
            improvement = c.one_level();
            double new_mod = c.modularity();
            g = c.partition2graph_binary();
            c = new Community(g, -1, precision);
        } while (improvement);
    }

    static class Graph {
        final int nodeSize;
        final long nb_links;
        final double total_weight;

        final long[] degrees;
        final int[] links;
        final float[] weights;

        /*
             binary file format is
             4 bytes for the number of nodes in the graph
             8*(nodeSize) bytes for the cumulative degree for each node:
                deg(0)=degrees[0]
                deg(k)=degrees[k]-degrees[k-1]
             4*(sum_degrees) bytes for the links
             IF WEIGHTED 4*(sum_degrees) bytes for the weights in a separate file
        */

        /**
         * @param filename   file with main information about graph
         * @param filename_w (nullable) file with link's weights
         */
        Graph(String filename, String filename_w) {
            degrees = new long[0];
            links = new int[0];
            weights = filename_w == null ? null : new float[0];
        }


        // return the number of neighbors (degree) of the node
        long nb_neighbors(int node) {
            assert node >= 0 && node < nodeSize;
            return node == 0 ? degrees[0] : degrees[node] - degrees[node - 1];
        }

        // return the number of self loops of the node
        double nb_selfloops(int node) {
            assert node >= 0 && node < nodeSize;
            for (int i = 0, p = neighbors(node); i < nb_neighbors(node); i++, p++) {
                if (links[p] == node) {
                    return weights == null ? 1. : weights[p];
                }
            }
            return 0.;
        }

        // return the weighted degree of the node
        double weighted_degree(int node) {
            assert node >= 0 && node < nodeSize;
            if (weights == null) {
                return nb_neighbors(node); //TODO ???? херня какая-то
            }
            double res = 0;
            for (int p = neighbors(node), i = 0; i < nb_neighbors(node); i++, p++) {
                res += weights[p];
            }
            return res;
        }

        // return pointers to the first neighbor and first weight of the node
        int neighbors(int node) {
            assert node >= 0 && node < nodeSize;
            assert weights != null;
            return node == 0 ? 0 : (int) degrees[node - 1];
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

            this.neigh_weight = new double[g.nodeSize];
            Arrays.fill(neigh_weight, -1);
            this.neigh_pos = new int[g.nodeSize];
            this.neigh_last = 0;

            this.n2c = new int[g.nodeSize];
            this.in = new double[g.nodeSize];
            this.tot = new double[g.nodeSize];

            for (int i = 0; i < g.nodeSize; i++) {
                this.n2c[i] = i;
                this.in[i] = g.nb_selfloops(i);
                this.tot[i] = g.weighted_degree(i);
            }

            this.nb_pass = nb_pass;
            this.min_modularity = min_modularity;
        }

        // initiliazes the partition with something else than all nodes alone
        void init_partition(String filename_part);

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
            for (int i = 0; i < g.nodeSize; i++) {
                if (tot[i] > 0) {
                    q += in[i] / g.total_weight - (tot[i] / g.total_weight) * (tot[i] / g.total_weight);
                }
            }
            return q;
        }

        // displays the graph of communities as computed by one_level
        void partition2graph() {
            int[] renumber = new int[g.nodeSize];
            Arrays.fill(renumber, -1);
            for (int node = 0; node < g.nodeSize; node++) {
                renumber[n2c[node]]++;
            }
            int final0 = 0;
            for (int i = 0; i < g.nodeSize; i++) {
                if (renumber[i] != -1) {
                    renumber[i] = final0++;
                }
            }
            for (int i = 0; i < g.nodeSize; i++) {
                for (int j = 0, p = g.neighbors(i); j < g.nb_neighbors(i); j++, p++) {
                    System.out.append(Integer.toString(renumber[n2c[i]])).append(' ')
                            .append(Integer.toString(renumber[n2c[g.links[p]]])).append('\n');
                }
            }
        }

        // displays the current partition (with communities renumbered from 0 to k-1)
        void display_partition() {
            int[] renumber = new int[g.nodeSize];
            Arrays.fill(renumber, -1);
            for (int node = 0; node < g.nodeSize; node++) {
                renumber[n2c[node]]++;
            }

            int final0 = 0;
            for (int i = 0; i < g.nodeSize; i++) {
                if (renumber[i] != -1) {
                    renumber[i] = final0++;
                }
            }

            for (int i = 0; i < g.nodeSize; i++) {
                System.out.append(Integer.toString(i)).append(' ')
                        .append(Integer.toString(renumber[n2c[i]])).append('\n');
            }
        }

        // generates the binary graph of communities as computed by one_level
        Graph partition2graph_binary();

        // compute communities of the graph for one level
        // return true if some nodes have been moved
        boolean one_level() {
            boolean improvement = false;
            int nb_moves;
            double new_mod = modularity();
            double cur_mod;

            int[] random_order = new int[g.nodeSize];
            for (int i = 0; i < g.nodeSize; i++) {
                random_order[i] = i;
            }
            for (int i = 0; i < g.nodeSize - 1; i++) {
                int rand_pos = ThreadLocalRandom.current().nextInt() % (g.nodeSize - i) + i;
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
                for (int node_tmp = 0; node_tmp < g.nodeSize; node_tmp++) {
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
