[![MIT License][license-shield]][license-url]


<!-- TABLE OF CONTENTS -->
## Table of Contents

* [About the Project](#about-the-project)
* [Build](#Build)
* [Usage](#usage)
* [License](#license)
* [Contact](#contact)


<!-- ABOUT THE PROJECT -->
## About The Project
최근 다양한 IoT 디바이스의 사용이 증가되고 있고, 그로 인한 보안 위협도 증가되고 있다. 베어메탈(BareMetal) IoT 디바이스의 펌웨어는 펌웨어 업데이트 파일 및 Flash De-soldering 등으로 추출이 가능 하며, 이를 역공학(Reverse Engineering) 툴을 이용한 정적 분석을 통해 실행 흐름을 분석하여 취약점을 찾을 수 있다. 이를 해결하기 위해 일반적인 컴퓨팅 시스템에는 정적 분석을 어렵게 하기 위한 다양한 소스코드 기반의 난독화 방법이 존재한다.그러나, 기존 바이너리 코드 난독화에 대한 연구는 다양하게 전개된 사례는 있으나, 베어메탈 기반의 IoT 디바이스를 타겟으로 하는 난독화 기법의 연구 전개는 미비한 상황이다.  이를 해결하기 위해 LLVM Pass를 이용한 난독화된 바이 너리 코드를 실행하는 코드의 삽입을 통해 베어메탈 IoT 디바이스 펌웨어의 바이너리 코드를 난독화 하는 방안을 제안한다.

<!-- BUILD -->
## Build
 
1. Clone the repo
```
git clone http://khuhub.khu.ac.kr/2020-1-capstone-design1/JJS_Project1.git
```

2. Install cmake
```
brew install cmake
```

3. Create Build folder
```
mkdir ./JJS_Project1/src/build
```

4. Change directory
```
cd ./JJS_Project1/src/build
```

5. Create LLVM Clang build file
```
cmake -DLLVM_ENABLE_PROJECTS=clang -G "Unix Makefiles" ../llvm
```

6. Build
```
make
```


<!-- USAGE EXAMPLES -->
## Usage
```
JJS_Project1/src/build/bin/clang -emit-llvm -c -S source.c -o source.ll
```
```
JJS_Project1/src/build/bin/opt -load JJS_Project1/src/build/lib/LLVMObfuscation.so -preprocess source.ll -o source.ll
```
```
JJS_Project1/src/build/bin/opt -load JJS_Project1/src/build/lib/LLVMObfuscation.so -rof source.ll -o source.ll
```

<!-- LICENSE -->
## License
LLVM([https://github.com/llvm-mirror/llvm](https://github.com/llvm-mirror/llvm))

<!-- CONTACT -->
## Contact
2015104175 박우진 - amdx1254@khu.ac.kr <br>
2017110275 이한솔 - mardi@khu.ac.kr

[license-shield]: https://img.shields.io/github/license/othneildrew/Best-README-Template.svg?style=flat-square
[license-url]: https://github.com/othneildrew/Best-README-Template/blob/master/LICENSE.txt
