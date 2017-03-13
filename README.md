nano-sm2
========

这是一个8位处理器上的SM2实现，未使用openssl等第三方库，目前仅支持256位SM2。代码基于nano-ecc实现（8位处理器上的ecc实现，详情见 https://github.com/iSECPartners/nano-ecc ）。

SM2与ecc的区别主要在于曲线参数的选择不同，另外在签名，验签的过程中也有一点区别，SM2的官方文档以及官方推荐参数可以参考 http://www.oscca.gov.cn/News/201012/News_1197.htm 。

Changes
--------

本代码主要在以下几方面对nano-ecc进行了改动：

 * 大数模运算 - nano-ecc在实现大数模运算的过程中，根据《Mathematical routines for the NIST prime elliptic curves》文档（https://koclab.cs.ucsb.edu/teaching/cren/docs/w02/nist-routines.pdf ）给出的方法，对模标准ecc参数p的运算进行了优化，故其模运算仅适用于标准ecc的曲线参数（nano-ecc这一部分代码也是参考的linux内核源码）。本代码根据其优化方法，实现了对256位SM2算法的推荐参数的算法优化，可以快速得到与SM2推荐参数p相关的模运算结果；

 * 签名过程 - 本代码完全按照SM2签名过程实现；

 * 验签过程 - 本代码完全按照SM2验签过程实现。

Usage Notes
-----------

使用时只需将sm2.h与sm2.c加入自己的项目工程中，然后再include头文件sm2.h即可。test_sm2.c为一个测试算法的样例。密钥对可用apps/makekeys.c来生成。

Parameters
-----------

另附本代码使用的SM2官方推荐参数（256位）：  
椭圆曲线方程：y^2 = x^3 + ax + b  
曲线参数：  
p=FFFFFFFE FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF 00000000 FFFFFFFF FFFFFFFF  
a=FFFFFFFE FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF 00000000 FFFFFFFF FFFFFFFC  
b=28E9FA9E 9D9F5E34 4D5A9E4B CF6509A7 F39789F5 15AB8F92 DDBCBD41 4D940E93  
n=FFFFFFFE FFFFFFFF FFFFFFFF FFFFFFFF 7203DF6B 21C6052B 53BBF409 39D54123  
Gx=32C4AE2C 1F198119 5F990446 6A39C994 8FE30BBF F2660BE1 715A4589 334C74C7  
Gy=BC3736A2 F4F6779C 59BDCEE3 6B692153 D0A9877C C62A4740 02DF32E5 2139F0A0  

