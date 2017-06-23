/****************************************************************************
  FileName     [ parse.h ]
  PackageName  [ util ]
  Synopsis     [ parsing functions ]
  Author       [ music960633 ]
****************************************************************************/

#ifndef UTIL_PARSE_H_
#define UTIL_PARSE_H_

#include <string>
#include <vector>
#include <fstream>

std::string readUntil(std::ifstream& ifs, char end) {
  std::string str;
  char c;
  while (!ifs.eof()) {
    ifs.get(c);
    str += c;
    if (c == end) break;
  }
  return str;
}

std::string getLineSafe(std::ifstream& ifs) {
  std::string str;


  return str;
}

std::vector<std::string> split(const std::string& str, const std::string& sep) {
  unsigned n = str.size();
  std::vector<std::string> vec;
  std::string token;
  for (unsigned i = 0; i < n; ++i) {
    if (sep.find(str[i]) == std::string::npos) {
      token += str[i];
    } else if (token.size() > 0) {
      vec.push_back(token);
      token.clear();
    }
  }
  if (token.size() > 0)
    vec.push_back(token);
  return vec;
}

std::string myToString(unsigned n) {
  if (n == 0) return "0";
  std::string arr[10] = {"0", "1", "2", "3", "4", "5", "6", "7", "8", "9"};
  std::string ret = "";
  while (n) {
    ret = arr[n % 10] + ret;
    n /= 10;
  }
  return ret;
}

bool str2Int(const std::string& str, int& num) {
  num = 0;
  size_t i = 0;
  int sign = 1;
  if(str[0] == '-') { sign = -1; i = 1; }
  bool valid = false;
  for(; i < str.size(); ++i) {
    if(isdigit(str[i])) {
      num *= 10;
      num += int(str[i] - '0');
      valid = true;
    }
    else return false;
  }
  num *= sign;
  return valid;
}

#endif  // UTIL_PARSE_H_
