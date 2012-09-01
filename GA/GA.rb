#!/usr/bin/env ruby

TARGET="What an awesome algorithm this is."
VALID_CHARS= 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz .'.chars.to_a

fitness= lambda do |v|
  sum= 0
  v.chars.each_with_index {|c,i| sum += 1 if c == TARGET[i] }
  sum
end

def random_population(pop_size, str_len)
  pop= []
  pop_size.times{ pop<< random_string(str_len) }
  pop
end

def random_string(length)
  s= ''
  length.times{ s += VALID_CHARS.sample }
  s
end

def map_fitness(pop, fitness, r=nil)
  r ||= {}
  pop.each do |x|
    r[x] ||= fitness.call(x)
  end
  r
end

def reproduce(x,y, crossover_preservation)
  return [x,y] if rand > crossover_preservation
  split= rand(x.size - 1)
  a= x[0..split] + y[(split+1)..-1]
  b= y[0..split] + x[(split+1)..-1]
  [a,b]
end

def mutate(x)
  x= x.dup
  x[rand x.size]= VALID_CHARS.sample
  x
end

def random_selection(pop, fitness_map)
  total= pop.inject(0.0){|t,x| t + fitness_map[x]}
  return pop.sample if total == 0
  r= rand(total)
  t= 0.0
  pop.each do |x|
    t+= fitness_map[x]
    return x if r < t
  end
  raise "What?!"
end

def ga(options={})
  options= {
    pop_size: 400,
    str_len: nil,
    fitness: nil,
    stop: nil,
    mutate: nil,
    crossover_preservation: 0.98,
  }.merge(options)

  pop= random_population options[:pop_size], options[:str_len]
  fitness_map= map_fitness pop, options[:fitness]
  sex_cycles= pop.size / 2 + pop.size % 2
  options[:mutate] ||= 1.0 / options[:str_len]

  stop= false
  round= 0
  until stop
    new_pop= []

    min_fitness= fitness_map.values.min
    fitness_map2= {}
    fitness_map.each{|w,f| fitness_map2[w]= f - min_fitness + 1 }

    sex_cycles.times do
      x= random_selection(pop, fitness_map2)
      y= random_selection(pop, fitness_map2)
      child1,child2 = reproduce(x,y, options[:crossover_preservation])
      child1= mutate(child1) if rand < options[:mutate]
      child2= mutate(child2) if rand < options[:mutate]
      new_pop<< child1
      new_pop<< child2
    end

    pop= new_pop
    fitness_map= map_fitness pop, options[:fitness]
    pop.sort_by! {|x| fitness_map[x] }
    best= pop.last
    max_fitness= fitness_map[best]
    printf "#%5d - %2d/%2d - %s\n", round+=1, max_fitness, TARGET.size, best

    stop= options[:stop].call(max_fitness)
  end
end

ga fitness: fitness,
  str_len: TARGET.size,
  mutate: 0.2,
  stop: lambda{|f| f == TARGET.size }

