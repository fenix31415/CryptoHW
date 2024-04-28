#include <algorithm>
#include <cassert>
#include <iostream>
#include <random>
#include <vector>

using num = unsigned long long;

num power(num x, num y, num p)
{
  x = x % p;

  num ans = 1;

  if (x == 0) return 0;

  while (y > 0)
  {
    if (y & 1)
      ans = (ans * x) % p;
    y = y >> 1;
    x = (x * x) % p;
  }
  return ans;
}

using pair = std::pair<num, num>;

std::pair<num, num> match(std::vector<pair>& l1, std::vector<pair>& l2) {
  std::sort(l1.begin(), l1.end());
  std::sort(l2.begin(), l2.end());

  num x = 0, y = 0;
  while (x < l1.size() && y < l2.size())
  {
    if (l1[x].first == l2[y].first)
      return { l1[x].second, l2[y].second };

    while (x < l1.size() && l1[x].first < l2[y].first)
      ++x;
    if (x >= l1.size())
      break;

    while (y < l2.size() && l1[x].first > l2[y].first)
      ++y;
  }
  // usually unreachable unless g is not a primitive root or random algorithm failed
  return {};
}

using snum = long long;
num gcd(num a, num b, snum& x, snum& y) {
  if (a < b)
    std::swap(a, b);

  x = 1, y = 0;
  num x1 = 0, y1 = 1, a1 = a, b1 = b;
  while (b1) {
    num q = a1 / b1;
    std::tie(x, x1) = std::make_tuple(x1, x - q * x1);
    std::tie(y, y1) = std::make_tuple(y1, y - q * y1);
    std::tie(a1, b1) = std::make_tuple(b1, a1 - q * b1);
  }
  return a1;
}

namespace task21 {
  std::vector<num> factorize(num n) {
    std::vector<num> ans;

    for (num i = 2; i * i <= n; i += static_cast<num>(1) + (i > 2)) {
      while ((n % i) == 0) {
        ans.push_back(i);
        n /= i;
      }
    }

    if (n != 1)
      ans.push_back(n);

    return ans;
  }

  std::vector<num> factorize_unique(num n) {
    std::vector<num> ans;

    for (num i = 2; i * i <= n; i += static_cast<num>(1) + (i > 2)) {
      bool added = false;
      while ((n % i) == 0) {
        if (!added) {
          ans.push_back(i);
          added = true;
        }
        n /= i;
      }
    }

    if (n != 1)
      ans.push_back(n);

    return ans;
  }

  bool IsPrimitive(num p, num g) {
    g = g % p;

    if (g == 0)
      return false;

    if (g == 1 && p != 2)
      return false;

    auto fs = factorize_unique(p - 1);
    for (auto f : fs)
    {
      if (power(g, (p - 1) / f, p) == 1)
        return false;
    }
    return true;
  }

  num BruteForce(num p, num g, num a) {
    g = g % p;
    a = a % p;

    num gx = 1;

    for (num x = 0; x < p; x++, gx = (gx * g) % p)
    {
      if (gx == a)
        return x;
    }
    // unreachable if g is primitive
    assert(false);
    return 0;
  }
}

namespace task26 {
  num babygiant(num p, num g, num a) {
    num n = std::sqrt(p);
    num u = power(g, p - 1 - n, p);

    std::vector<pair> l1;
    std::vector<pair> l2;
    num v1 = 1;
    num v2 = a;
    for (num i = 0; i <= n; i++, v1 = (v1 * g) % p, v2 = (v2 * u) % p)
    {
      l1.push_back({ v1, i });
      l2.push_back({ v2, i });
    }

    auto [x, y] = match(l1, l2);
    return x + n * y;
  }
}

namespace task27 {
  num prop(num p, num g, num a) {
    num n = std::sqrt(9 * p);

    std::random_device rnd_device;
    std::mt19937 en(rnd_device());
    std::uniform_int_distribution<num> dist(1, p);

    using pair = std::pair<num, num>;
    std::vector<pair> l1;
    std::vector<pair> l2;
    for (num i = 0; i < n; i++)
    {
      num power1 = dist(en);
      num power2 = dist(en);
      l1.push_back({ power(g, power1, p), power1 });
      l2.push_back({ (a * power(g, power2, p)) % p, power2 });
    }

    auto [x, y] = match(l1, l2);
    return (p - 1 + x - y) % (p - 1);
  }
}

namespace task28 {
  num PollardP(num p, num g, num a) {
    std::vector<num> X, A, B;

    const num P_div_3 = p / 3;
    const num P_div_3_mul_2 = P_div_3 * 2;
    const num P_sub_1 = p - 1;

    X.push_back(1);
    A.push_back(0);
    B.push_back(0);

    auto f = [=](num x) {
      if (x < P_div_3)
        return (g * x) % p;
      if (x < P_div_3_mul_2)
        return (x * x) % p;
      return (a * x) % p;
      };

    auto fa = [=](num x, num a_old) {
      if (x < P_div_3)
        return (a_old + 1) % P_sub_1;
      if (x < P_div_3_mul_2)
        return (2 * a_old) % P_sub_1;
      return a_old;
      };

    auto fb = [=](num x, num b_old) {
      if (x < P_div_3)
        return b_old;
      if (x < P_div_3_mul_2)
        return (2 * b_old) % P_sub_1;
      return (b_old + 1) % P_sub_1;
      };

    auto step = [&]() {
      num x = X.back();
      X.push_back(f(x));
      num b_old = B.back();

      A.push_back(fa(x, A.back()));
      B.push_back(fb(x, B.back()));

      assert((power(g, A.back(), p) * power(a, B.back(), p)) % p == X.back());
      };

    do 
    {
      step();
    } while (X.size() % 2 == 0 || X.back() != X[(X.size() - 1) / 2]);

    num xi = X[(X.size() - 1) / 2];
    num x2i = X.back();

    assert(X.size() % 2 == 1);
    assert(x2i == xi);

    num al = A[(A.size() - 1) / 2];
    num be = B[(B.size() - 1) / 2];
    num ga = A.back();
    num de = B.back();

    // g^al a^be = g^ga a^de
    assert((power(g, al, p) * power(a, be, p)) % p == (power(g, ga, p) * power(a, de, p)) % p);

    // g^(al - ga) = a^(de - be)
    num g_pow = (P_sub_1 + al - ga) % P_sub_1;
    num a_pow = (P_sub_1 + de - be) % P_sub_1;

    snum tmp = 0, spow = 0;
    num d = gcd(a_pow, P_sub_1, tmp, spow);

    num pow = static_cast<num>(spow);

    pow = (P_sub_1 + pow) % P_sub_1;
    pow = (g_pow * static_cast<num>(pow)) % P_sub_1;

    pow /= d;
    num new_P_sub_1 = P_sub_1 / d;

    num mult = power(g, new_P_sub_1, p);
    num val = power(g, pow, p);
    for (; pow < p; pow += new_P_sub_1, val = (val * mult) % p)
    {
      if (val == a) {
        return pow;
      }
    }
    // unreachable
    assert(false);
    return 0;
  }
}

namespace tests {
  void assert_eq(num val, num expected) {
    if (val != expected)
      std::cout << val << " != " << expected << "\n";
    assert(val == expected);
  }

  void test_log(num(*f)(num p, num g, num a)) {
    std::cout << "Test log\n";

    assert_eq(f(48611, 19, 24717), 37869);
    assert_eq(f(2000000011, 10, 1), 0);

    assert_eq(f(2000000011, 2, 215297950), 1000);
    assert_eq(f(2000000011, 10, 1650752415), 1001);
    assert_eq(f(2000000011, 98, 1733669444), 27182818);
    assert_eq(f(2000000011, 156, 400712253), 123456789);
    assert_eq(f(2000000011, 2000000002, 1548512313), 314159);
    assert_eq(f(2000000011, 2000000007, 932008895), 314160);
    
    num p = 1000000007;
    std::vector<num> gs = { 5,10,13,15,17,19,20, 999999998 , 999999999 ,1000000000, 1000000001, 1000000003, 1000000004,1000000005 };
    std::vector<num> as = { 1,2,3,4,5,6,10,100,1000,10000,100000,1000000006 };
    // don't call with brute force, too long
    for (auto g : gs)
    {
      for (auto a : as)
      {
        num x = f(p, g, a);
        num ans = power(g, x, p);
        assert_eq(ans, a);
      }
    }
  }

  void tests() {
    {
      using task21::IsPrimitive;

      assert(IsPrimitive(101, 2));
      assert(IsPrimitive(101, 3));
      assert(!IsPrimitive(101, 4));
      assert(!IsPrimitive(101, 5));
      assert(!IsPrimitive(101, 6));
      assert(IsPrimitive(101, 7));
      assert(IsPrimitive(101, 8));
      assert(IsPrimitive(101, 99));

      // 5 10 13 15 17 19 20 1000000000 1000000001 1000000003 1000000004 1000000005
      assert(!IsPrimitive(1000000007, 0));
      assert(!IsPrimitive(1000000007, 1));
      assert(!IsPrimitive(1000000007, 2));
      assert(!IsPrimitive(1000000007, 3));
      assert(!IsPrimitive(1000000007, 4));
      assert(IsPrimitive(1000000007, 5));
      assert(!IsPrimitive(1000000007, 6));
      assert(!IsPrimitive(1000000007, 7));
      assert(!IsPrimitive(1000000007, 8));
      assert(!IsPrimitive(1000000007, 9));
      assert(IsPrimitive(1000000007, 10));
      assert(!IsPrimitive(1000000007, 11));
      assert(!IsPrimitive(1000000007, 12));
      assert(IsPrimitive(1000000007, 13));
      assert(!IsPrimitive(1000000007, 14));
      assert(IsPrimitive(1000000007, 15));
      assert(!IsPrimitive(1000000007, 16));
      assert(IsPrimitive(1000000007, 17));
      assert(!IsPrimitive(1000000007, 18));
      assert(IsPrimitive(1000000007, 19));
      assert(IsPrimitive(1000000007, 20));
      assert(!IsPrimitive(1000000007, 21));

      assert(IsPrimitive(1000000007, 1000000000 - 5));
      assert(IsPrimitive(1000000007, 1000000000 - 4));
      assert(!IsPrimitive(1000000007, 1000000000 - 3));
      assert(IsPrimitive(1000000007, 1000000000 - 2));
      assert(IsPrimitive(1000000007, 1000000000 - 1));
      assert(IsPrimitive(1000000007, 1000000000));
      assert(IsPrimitive(1000000007, 1000000001));
      assert(!IsPrimitive(1000000007, 1000000002));
      assert(IsPrimitive(1000000007, 1000000003));
      assert(IsPrimitive(1000000007, 1000000004));
      assert(IsPrimitive(1000000007, 1000000005));
      assert(!IsPrimitive(1000000007, 1000000006));
      assert(!IsPrimitive(1000000007, 1000000007));
    }

    //test_log(task21::BruteForce);
    test_log(task26::babygiant);
    test_log(task27::prop);
    test_log(task28::PollardP);
  }
}

int main() {
  tests::tests();
}
