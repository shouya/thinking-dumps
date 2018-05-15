#!/usr/bin/env ruby
#
# This tool is used to convert problems using with nodes ordered by their degrees
# and convert the solution according to the input
#

require 'byebug'

class Solution
  def from_solution(sol)
  end
end

class Input
  attr_accessor :n_nodes, :n_edges,
                :edges,
                :map_from_ordered,
                :map_from_original,
                :node_degree

  def initialize
    @n_nodes = 0
    @n_edges = 0
    @edges = []

    @map_from_ordered = {}
    @map_from_original = {}
    @node_degree = Hash.new(0)
  end

  def self.from_str(str)
    new.tap {|x| x.from_str(str) }
  end

  def from_str(input)
    meta, *edges = input.lines.map(&:chomp).map(&:split).map{|x| x.map(&:to_i) }
    @n_nodes, @n_edges = meta
    edges.each do |(a,b)|
      @edges << [a,b]
      @node_degree[a] += 1
      @node_degree[b] += 1
    end
  end

  def convert!
    # higher degree nodes comes first!
    @node_degree.to_a.sort_by(&:last).reverse.each_with_index do |(n, _), new_i|
      @map_from_ordered[new_i] = n
      @map_from_original[n] = new_i
    end

    new_edges = []
    @edges.each do |(a,b)|
      new_edges << [@map_from_original[a], @map_from_original[b]]
    end
    @edges = new_edges
  end

  def to_str
    out = "#{@n_nodes} #{@n_edges}\n"
    @edges.each do |(a,b)|
      out << "#{a} #{b}\n"
    end
    out
  end

  def to_dzn
    out = "n_nodes = #{@n_nodes};\n"
    out << "n_edges = #{@n_edges};\n"
    edge_str = @edges.map {|n1,n2| "#{n1},#{n2}," }.join('|')
    out << "edges = [|#{edge_str}|];\n"
    orig_order = @map_from_original.to_a.sort_by(&:first).map(&:last)
    out << "orig_nodes = [#{orig_order.join(',')}];\n"
    out
  end
end

def main
  case ARGV.shift.intern
  when :input
    # convert input
    if ARGV.first
      input_str = File.read(ARGV.first)
    else
      input_str = $stdin.read
    end
    input = Input.from_str(input_str)
    input.convert!
    puts input.to_dzn

  when :solution
    # convert solution

  end
end


main
