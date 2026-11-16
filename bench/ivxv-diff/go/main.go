// Our code, built against an unmodified IVXV checkout (CC BY-NC-ND 3.0):
// the decryption proofs of the IVXV Go core library (tivi.io/core,
// crypto/elgamal: PrivateKey.Prove, PublicKey.Verify) at RFC3526ModPGroup2048.
//
//	ivxvgo group                     prints the group's p, q, g (decimal)
//	ivxvgo prove STATEMENTS.tsv      lines "x c1 c2 s salt": Prove with the
//	                                 random scalar s (deterministic); prints
//	                                 "pk proof" (hex DER); salt is hex, "-" for none
//	ivxvgo verify CASES.tsv          lines "pk proof salt" (hex DER): the key by
//	                                 ASN1UnmarshalPublicElement, then
//	                                 PublicKey.Verify; prints true | false<TAB>error
package main

import (
	"bufio"
	"encoding/hex"
	"fmt"
	"math/big"
	"os"
	"strings"

	"golang.org/x/crypto/cryptobyte"
	"tivi.io/core/crypto/elgamal"
	"tivi.io/core/math/group"
	_ "tivi.io/core/math/group/all"
)

func intDER(x *big.Int) []byte {
	var b cryptobyte.Builder
	b.AddASN1BigInt(x)
	out, err := b.Bytes()
	if err != nil {
		panic(err)
	}
	return out
}

func num(s string) *big.Int {
	x, ok := new(big.Int).SetString(s, 10)
	if !ok {
		panic("number " + s)
	}
	return x
}

func saltOf(s string) []byte {
	if s == "-" {
		return nil
	}
	b, err := hex.DecodeString(s)
	if err != nil {
		panic(err)
	}
	return b
}

func main() {
	G, err := group.Get("RFC3526ModPGroup2048")
	if err != nil {
		panic(err)
	}
	params := elgamal.NewParameters(G)
	if os.Args[1] == "group" {
		gder, _ := G.Generator().Marshal()
		fmt.Println(G.Order().String(), hex.EncodeToString(gder))
		return
	}
	f, err := os.Open(os.Args[2])
	if err != nil {
		panic(err)
	}
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1<<20), 1<<24)
	for sc.Scan() {
		l := sc.Text()
		if strings.TrimSpace(l) == "" {
			continue
		}
		fs := strings.Split(l, "\t")
		switch os.Args[1] {
		case "prove":
			key, err := elgamal.NewPrivateKey(params, group.NewScalar(num(fs[0]), G.Order()))
			if err != nil {
				panic(err)
			}
			A, err1 := G.ElementOf(intDER(num(fs[1])))
			B, err2 := G.ElementOf(intDER(num(fs[2])))
			if err1 != nil || err2 != nil {
				panic(fmt.Sprint(err1, err2))
			}
			ctDer, err := elgamal.NewCiphertext(A, B).MarshalASN1()
			if err != nil {
				panic(err)
			}
			dec, err := key.Decrypt(ctDer, false)
			if err != nil {
				panic(err)
			}
			proof, err := key.Prove(group.NewScalar(num(fs[3]), G.Order()), ctDer, dec, saltOf(fs[4]))
			if err != nil {
				panic(err)
			}
			pk, err := key.Public().Marshal()
			if err != nil {
				panic(err)
			}
			fmt.Printf("%s\t%s\n", hex.EncodeToString(pk), hex.EncodeToString(proof))
		case "verify":
			r := func() (res string) {
				defer func() {
					if e := recover(); e != nil {
						res = fmt.Sprintf("false\tpanic: %v", e)
					}
				}()
				pkb, err1 := hex.DecodeString(fs[0])
				pb, err2 := hex.DecodeString(fs[1])
				if err1 != nil || err2 != nil {
					return "false\thex"
				}
				y, err := elgamal.ASN1UnmarshalPublicElement(G, pkb)
				if err != nil {
					return "false\t" + strings.ReplaceAll(err.Error(), "\t", " ")
				}
				if err := elgamal.NewPublicKey(params, y).Verify(pb, saltOf(fs[2])); err != nil {
					return "false\t" + strings.ReplaceAll(err.Error(), "\t", " ")
				}
				return "true"
			}()
			fmt.Println(r)
		}
	}
}
