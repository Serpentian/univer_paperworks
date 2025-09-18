#include "user/include/task.hpp"

#include <cmath>
#include <sstream>
#include <vector>

namespace abeille {
namespace user {

std::vector<int> primeFactors(int n) {
  std::vector<int> prime_factors;
  while (n % 2 == 0) {
    n /= 2;
    prime_factors.push_back(2);
  }

  for (int i = 3; i <= std::sqrt(n); i = i + 2) {
    while (n % i == 0) {
      n = n / i;
      prime_factors.push_back(i);
    }
  }

  if (n > 2) {
    prime_factors.push_back(n);
  }

  return prime_factors;
}

error ProcessTaskData(const Task::Data &task_data, Task::Result &task_result) {
  for (int elem : task_data.data()) {
    auto result = task_result.add_result();
    result->set_number(elem);

    for (int factor : primeFactors(elem)) {
      result->add_prime_factors(factor);
    }
  }

  return error();
}

}  // namespace user
}  // namespace abeille
