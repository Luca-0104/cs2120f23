from itertools import permutations

def generate_all_permutations(lst):
    all_permutations = []
    
    # Generate permutations for all possible lengths
    for length in range(1, len(lst) + 1):
        current_permutations = permutations(lst, length)
        all_permutations.extend(["#reduce " + ' '.join(map(str, perm)) for perm in current_permutations])
    
    return all_permutations

# Example usage:
my_list = ["do_map", "box_functor", "Nat.succ", "(Box.contents 1)", "<$>"]
all_possible_permutations = generate_all_permutations(my_list)

# Print the result
for permutation in all_possible_permutations:
    print(permutation)