#! /usr/local/bin/perl -w

#### Program to simulate an epidemic on a social graph
#### Written by David A. Madore <URL: http://www.madore.org/~david >
#### Initial version: 2020-03-21
#### This version:    2020-03-21
#### License: CC-BY 4.0 <URL: http://creativecommons.org/licenses/by/4.0/ >

## This program generates a social graph using methods inspired by the
## paper "Emergence of Scaling in Random Networks" by Barabási and
## Albert (*Science* 286 (1999) 509-512) and then runs a stochastic
## epidemiological model on the graph.

## More precisely, there are two steps to this program:

## First, generate a "social" graph with nbnodes vertices (nodes,
## i.e., individuals), and an average of edges_per_node edge/vertex
## ratio.  The structure of this graph is crucially determined by the
## "prob_unbiased" parameter: 0 will give a random graph, 1 will give
## a graph following essentially the Barabási & Albert model.  More
## precisely, the graph is constructed one node at a time: each added
## node is connected to a number of other nodes following an
## exponential distribution +1; each node to be connected with is
## selected either purely at random among all nodes (with probability
## prob_unbiased), or else as a random vertex of a random edge
## (favoring already highly connected nodes).

## Once this graph is generated, start running an epidemic on it.  The
## epidemic follows a SEIR system, where each individual is
## successively susceptible (S), exposed (E), infectious (I) and
## recovered (R).  Once infected, it moves to the E state, then moves
## to the I and R states after fixed times given by incubation_time
## and recovery_time.  At each step during the I state, the individual
## will perform two kinds of infections: with probability given by
## contagiousness, it infects each one of its neighbors in the social
## graph; and with probability given by extra_random_contagiousness,
## it infects a purely random node in the graph.

## The epidemic is seeded by init_seeds nodes, marked as exposed, at
## random.

## The program outputs three kinds of data:

## - On the standard output, a tab-separated timeline of the epidemic,
##   each line giving the time step and the population count of
##   S,E,I,R nodes.

## - On file descriptor 3 (redirect with 3>gens.dat under Unix), the
##   number of nodes infected at each generation (initial seeds are
##   generation 0, and each individual first infected by an individual
##   of generation g is marked of generation g+1).

## - On the standard error (file descriptor 2), various basic
##   statistics: the final attack rate (number of recovered
##   individuals over total population), peak infectious rates, number
##   of attempted contaminations, the maximal slope over 20 time steps
##   of the log of the number of infected cases (ignoring values which
##   are too low), and the maximal generational reproduction number
##   over 2 generations (again ignoring values which are too low), so
##   as to make comparisons possible.

use strict;
use warnings;

use constant {
    ### Social network parameters ###
    ## Number of nodes
    nbnodes => 300000,
    ## Average number of edges per node
    edges_per_node => 5,
    ## Probability of connecting to a random node instead of a random edge
    prob_unbiased => 0.2,

    ### Epidemic parameters ###
    ## Initial number of infected
    init_seeds => 20,
    ## Contagiousness per time step
    contagiousness => 0.009,
    ## Recovery time (number of steps) starting at infection
    recovery_time => 30,
    ## Incubation period (number of steps) starting at infection
    incubation_time => 5,
    ## Probability of purely random contamination (outside social graph)
    extra_random_contagiousness => 0.01
};

printf STDERR "prob_unbiased = %f, contagiousness = %f, extra_random_contagiousness = %f\n", prob_unbiased, contagiousness, extra_random_contagiousness;

## Nodes of the social graph, each a ref to a hash of connected nodes
my @social_graph;

sub generate_social_graph {
    my @social_edges;
    for ( my $i=0 ; $i<nbnodes ; $i++ ) {
	## Create a new node
	push @social_graph, {};
	do {
	    ## Now connect it to various other nodes
	    my $k;  ## Node to connect
	    if ( scalar(@social_edges) == 0 || rand(1) < prob_unbiased ) {
		## Choose random node
		$k = int(rand(scalar(@social_graph)));
	    } else {
		## Choose random vertex of random edge
		$k = $social_edges[int(rand(scalar(@social_edges)))][int(rand(2))];
	    }
	    if ( $k != $i && ! $social_graph[$i]{$k} ) {
		## Connect node $i to node $k
		$social_graph[$i]{$k} = 1;
		$social_graph[$k]{$i} = 1;
		push @social_edges, [$i, $k];
	    }
	} while ( rand(edges_per_node) >= 1 );
    }
    printf STDERR "social network has %d nodes, %d edges\n", scalar(@social_graph), scalar(@social_edges);
}

generate_social_graph;

# print "graph social {\n";
# for ( my $i=0 ; $i<scalar(@social_graph) ; $i++ ) {
#     printf "\tn%d;\n", $i;
#     foreach my $k ( keys(%{$social_graph[$i]}) ) {
# 	if ( $k < $i ) {
# 	    printf "\tn%d--n%d;\n", $i, $k;
# 	}
#     }
# }
# print "}\n";

# for ( my $i=0 ; $i<scalar(@social_graph) ; $i++ ) {
#     printf "%d\n", scalar(keys(%{$social_graph[$i]}));
# }

## The state of each node
## (undef: susceptible; 0: exposed; 1: infected; 2: recovered)
my @epidemic_state;
## Time since infection for each node
my @epidemic_timer;
## Generation at which each node was infected
my @epidemic_generations;
## Set of currently infected nodes
my %infected_pool;
## Number of currently susceptible, infected and recovered ndoes
my $nb_susceptible = scalar(@social_graph);
my $nb_exposed = 0;
my $nb_infectious = 0;
my $nb_recovered = 0;
## Size of each generation
my @generation_counts;
## History of stats
my @history;
## More stats
my $peak_infected = -1;
my $peak_infected_step;
my $peak_infected_attack;
my $peak_infectious = -1;
my $peak_infectious_step;
my $peak_infectious_attack;
my $total_attempted_infections = 0;
my $peak_attempted_infections = -1;
my $peak_attempted_infections_step;
my $peak_actual_infections = -1;
my $peak_actual_infections_step;

sub infect {
    ## Mark a node as infected
    my $i = shift;  ## Node to infect
    my $g = shift;  ## Generation
    if ( ! defined($epidemic_state[$i]) ) {
	## Node is susceptible => infect it
	$epidemic_state[$i] = 0;  ## Start incubating
	$epidemic_timer[$i] = 0;  ## Start counting
	die "this shouldn't happen" if defined($infected_pool{$i});
	$infected_pool{$i} = 1;  ## Place it in the infected pool
	die "this shouldn't happen" if defined($epidemic_generations[$i]);
	$epidemic_generations[$i] = $g;  ## Record generation
	## Update stats:
	$nb_susceptible--;
	$nb_exposed++;
	$generation_counts[$g]++;
	return 1;
    } else {
	return 0;
    }
}

my $step;

sub step_time {
    ## Forward one time step
    my $attempted_infections = 0;
    my $actual_infections = 0;
    my @l = keys(%infected_pool);
    foreach my $i ( @l ) {
	my $st = $epidemic_state[$i];
	$epidemic_timer[$i]++;  ## Step time forward
	die "this shouldn't happen" unless $st==0 || $st==1;
	if ( $st == 0 && $epidemic_timer[$i] >= incubation_time ) {
	    ## Node is now infectious
	    $epidemic_state[$i] = 1;
	    $st = 1;
	    $nb_exposed--;
	    $nb_infectious++;
	} elsif ( $epidemic_timer[$i] >= recovery_time ) {
	    ## Node has recovered
	    $epidemic_state[$i] = 2;
	    $st = 2;
	    die "this shouldn't happen" unless defined($infected_pool{$i});
	    delete $infected_pool{$i};
	    $nb_infectious--;
	    $nb_recovered++;
	}
	if ( $st == 1 ) {
	    my $g = $epidemic_generations[$i];
	    ## Infect some neighbors
	    foreach my $k (keys(%{$social_graph[$i]})) {
		die "this shouldn't happen" unless defined($g);
		if ( rand(1) < contagiousness ) {
		    $attempted_infections++;
		    $actual_infections += infect($k, $g+1);
		}
	    }
	    ## Infect purely random node
	    if ( rand(1) < extra_random_contagiousness ) {
		$attempted_infections++;
		$actual_infections += infect(int(rand(scalar(@social_graph))), $g+1);
	    }
	}
    }
    if ( $nb_exposed + $nb_infectious > $peak_infected ) {
	$peak_infected = $nb_exposed + $nb_infectious;
	$peak_infected_step = $step;
	$peak_infected_attack = $nb_exposed + $nb_infectious + $nb_recovered;
    }
    if ( $nb_infectious > $peak_infectious ) {
	$peak_infectious = $nb_infectious;
	$peak_infectious_step = $step;
	$peak_infectious_attack = $nb_exposed + $nb_infectious + $nb_recovered;
    }
    $total_attempted_infections += $attempted_infections;
    if ( $attempted_infections > $peak_attempted_infections ) {
	$peak_attempted_infections = $attempted_infections;
	$peak_attempted_infections_step = $step;
    }
    if ( $actual_infections > $peak_actual_infections ) {
	$peak_actual_infections = $actual_infections;
	$peak_actual_infections_step = $step;
    }
}

## Initially infect init_seeds nodes
for ( my $i=0 ; $i<init_seeds ; $i++ ) {
    infect(int(rand(scalar(@social_graph))), 0);
}

## Now run the simulation
for ( $step=0 ; scalar(%infected_pool) ; $step++ ) {
    ## Record stats history
    push @history, [$step, $nb_susceptible, $nb_exposed, $nb_infectious, $nb_recovered];
    printf "%d\t%d\t%d\t%d\t%d\n", $step, $nb_susceptible, $nb_exposed, $nb_infectious, $nb_recovered;
    step_time;
}

## Output per-generation stats on file descriptior 3
open GENSTATS, ">&=3";
for ( my $g=0 ; defined($generation_counts[$g]) ; $g++ ) {
    printf GENSTATS "%d\t%d\n", $g, $generation_counts[$g];
}
close GENSTATS;

printf STDERR "finished in %d steps\n", $step;
printf STDERR "final attack rate: %f\n", $nb_recovered/scalar(@social_graph);
printf STDERR "peak infected fraction: %f (at step %d: attack rate %f)\n", $peak_infected/scalar(@social_graph), $peak_infected_step, $peak_infected_attack/scalar(@social_graph);
printf STDERR "peak infectious fraction: %f (at step %d: attack rate %f)\n", $peak_infectious/scalar(@social_graph), $peak_infectious_step, $peak_infectious_attack/scalar(@social_graph);
printf STDERR "total attempted infections: %d\n", $total_attempted_infections;
printf STDERR "peak attempted infections: %d (at step %d)\n", $peak_attempted_infections, $peak_attempted_infections_step;
printf STDERR "peak actual infections: %d (at step %d)\n", $peak_actual_infections, $peak_actual_infections_step;

my $slope_ival = 20;
my $maxslope = 0;  my $maxslope_step = -1;
for ( $step=0 ; $step<scalar(@history)-$slope_ival ; $step++ ) {
    if ( $history[$step][3] > sqrt(nbnodes) ) {
	my $thisslope = ($history[$step+$slope_ival][2]+$history[$step+$slope_ival][3])/($history[$step][2]+$history[$step][3]);
	if ( $thisslope > $maxslope ) {
	    $maxslope = $thisslope;
	    $maxslope_step = $step;
	}
    }
}

printf STDERR "max log slope of infected cases is: %f per time step (between steps %d and %d)\n", log($maxslope)/$slope_ival, $maxslope_step, $maxslope_step+$slope_ival;

my $repnum_ival = 2;
my $maxrepnum = 0;  my $maxrepnumg = -1;
for ( my $g=0 ; $g<scalar(@generation_counts)-1 ; $g++ ) {
    if ( $generation_counts[$g] > sqrt(nbnodes) ) {
	my $thisrepnum = $generation_counts[$g+$repnum_ival]/$generation_counts[$g];
	if ( $thisrepnum > $maxrepnum ) {
	    $maxrepnum = $thisrepnum;
	    $maxrepnumg = $g;
	}
    }
}

printf STDERR "max generational reproduction number is: %f (between gens %d and %d)\n", exp(log($maxrepnum)/$repnum_ival), $maxrepnumg, $maxrepnumg+$repnum_ival;
