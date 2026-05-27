package HanYU.Miao;

import it.unisa.dia.gas.jpbc.*;
import it.unisa.dia.gas.plaf.jpbc.pairing.PairingFactory;
import it.unisa.dia.gas.plaf.jpbc.pairing.a.TypeACurveGenerator;

import java.math.BigInteger;
import java.util.*;

public class Miao {

    static Pairing pairing;
    static Field G1, GT, Zr;

    static Element g;

    static Element[] gArray;

    static Element u1, u2, u3, u4, V;

    static Element gamma, nu, alpha;

    static Map<String, Element> AjMap =
            new HashMap<>();

    static int n = 100;

    // =========================
    // Hash
    // =========================

    static Element H0(String s) {

        return Zr.newElement()
                .setFromHash(
                        s.getBytes(),
                        0,
                        s.length())
                .getImmutable();
    }

    static byte[] H(Element e) {

        return e.toBytes();
    }

    static Element hf1(
            String tau,
            String w) {

        return G1.newElement()
                .setFromHash(
                        (tau + w).getBytes(),
                        0,
                        (tau + w).length())
                .getImmutable();
    }

    static Element hf2(
            String w,
            Element sigma) {

        return G1.newElement()
                .setFromHash(
                        (w + sigma.toString()).getBytes(),
                        0,
                        (w + sigma.toString()).length())
                .getImmutable();
    }

    static Element hf4(byte[] b) {

        return Zr.newElement()
                .setFromHash(
                        b,
                        0,
                        b.length)
                .getImmutable();
    }

    // =========================
    // Keys
    // =========================

    static class CSKey {

        Element pk;
        Element sk;
    }

    static class WSKey {

        Element pk;
        Element sk;
    }

    static class DOKey {

        Element pk1, pk2;

        Element sk1, sk2;
    }

    static class DUKey {

        Element K1, K2, K3;
    }

    // =========================
    // Ciphertext
    // =========================

    static class Ciphertext {

        Element W0, W1, W2;

        byte[] W3;

        Element C;
        Element Cp;
        Element CR;

        List<String> pbf;

        byte[] encMessage;
    }

    // =========================
    // Trapdoor
    // =========================

    static class Trapdoor {

        Element T1;
        Element T2;
    }

    // =========================
    // Setup
    // =========================

    static void setup(
            int attrNum) {

        TypeACurveGenerator pg =
                new TypeACurveGenerator(
                        160,
                        512);

        PairingParameters params =
                pg.generate();

        pairing =
                PairingFactory.getPairing(params);

        G1 = pairing.getG1();
        GT = pairing.getGT();
        Zr = pairing.getZr();

        g =
                G1.newRandomElement()
                        .getImmutable();

        alpha =
                Zr.newRandomElement()
                        .getImmutable();

        gamma =
                Zr.newRandomElement()
                        .getImmutable();

        nu =
                Zr.newRandomElement()
                        .getImmutable();

        gArray =
                new Element[2 * n + 2];

        for (int i = 1;
             i <= 2 * n;
             i++) {

            gArray[i] =
                    g.powZn(
                            alpha.pow(BigInteger.valueOf(i))
                    ).getImmutable();
        }

        u2 =
                G1.newRandomElement();

        u3 =
                G1.newRandomElement();

        u4 =
                G1.newRandomElement();

        u1 =
                g.powZn(gamma);

        V =
                g.powZn(nu);

        for (int i = 0;
             i < attrNum;
             i++) {

            String att =
                    "ATTR" + i;

            Element aj =
                    Zr.newRandomElement();

            AjMap.put(
                    att,
                    u4.powZn(aj)
            );
        }
    }

    // =========================
    // CS KeyGen
    // =========================

    static CSKey csKeyGen() {

        CSKey key =
                new CSKey();

        key.sk =
                Zr.newRandomElement();

        key.pk =
                g.powZn(key.sk);

        return key;
    }

    // =========================
    // WS KeyGen
    // =========================

    static WSKey wsKeyGen() {

        WSKey key =
                new WSKey();

        key.sk =
                Zr.newRandomElement();

        key.pk =
                g.powZn(key.sk);

        return key;
    }

    // =========================
    // DO KeyGen
    // =========================

    static DOKey doKeyGen(
            int index) {

        DOKey key =
                new DOKey();

        key.sk1 =
                Zr.newRandomElement();

        key.sk2 =
                Zr.newRandomElement();

        key.pk1 =
                gArray[index]
                        .powZn(key.sk1);

        key.pk2 =
                gArray[index]
                        .powZn(key.sk2);

        return key;
    }

    // =========================
    // DU KeyGen
    // =========================

    static DUKey duKeyGen(
            List<String> attrs) {

        DUKey key =
                new DUKey();

        Element r =
                Zr.newRandomElement();

        Element prod =
                G1.newOneElement();

        for (String att : attrs) {

            prod =
                    prod.mul(
                            AjMap.get(att)
                    );
        }

        key.K1 =
                u2.powZn(gamma)
                        .mul(u3)
                        .mul(prod)
                        .powZn(r);

        key.K2 =
                g.powZn(r);

        key.K3 =
                G1.newRandomElement();

        return key;
    }

    // =========================
    // Keyword Warrant
    // =========================

    static Element keywordWarrant(
            String tau,
            String w,
            WSKey wsKey) {

        Element delta =
                Zr.newRandomElement();

        Element W =
                hf1(tau, w)
                        .mul(
                                g.powZn(delta)
                        );

        Element sigmaT =
                W.powZn(wsKey.sk);

        return sigmaT.mul(
                wsKey.pk.powZn(delta.negate())
        );
    }

    // =========================
    // Encrypt
    // =========================

    static Ciphertext encrypt(
            String message,
            String keyword,
            Element sigma,
            DOKey doKey,
            CSKey csKey,
            List<String> attrs) {

        Ciphertext ct =
                new Ciphertext();

        Element xi =
                Zr.newRandomElement();

        ct.W0 =
                g.powZn(xi);

        ct.W1 =
                ct.W0.powZn(doKey.sk1);

        ct.W2 =
                V.mul(doKey.pk2)
                        .mul(csKey.pk)
                        .powZn(xi);

        Element temp1 =
                pairing.pairing(
                        hf2(keyword, sigma),
                        g
                ).powZn(
                        xi.mul(doKey.sk1)
                );

        Element temp2 =
                pairing.pairing(
                        gArray[1],
                        gArray[n]
                ).powZn(
                        xi.mul(doKey.sk1)
                                .mul(doKey.sk2)
                );

        ct.W3 =
                H(temp1.div(temp2));

        Element s =
                Zr.newRandomElement();

        Element z =
                hf4(
                        (ct.W0.toString()
                                + ct.W1.toString())
                                .getBytes()
                );

        Element M =
                GT.newRandomElement();

        ct.C =
                pairing.pairing(
                                u1,
                                u2
                        ).powZn(s)
                        .mul(M);

        ct.Cp =
                g.powZn(
                        z.mul(s)
                );

        Element prod =
                u3.duplicate();

        for (String att : attrs) {

            prod =
                    prod.mul(
                            AjMap.get(att)
                    );
        }

        ct.CR =
                prod.powZn(
                        z.mul(s)
                );

        return ct;
    }

    // =========================
    // Trapdoor
    // =========================

    static Trapdoor trapdoor(
            String keyword,
            Element sigma,
            DUKey duKey,
            CSKey csKey) {

        Trapdoor td =
                new Trapdoor();

        Element y =
                Zr.newRandomElement();

        td.T2 =
                g.powZn(y);

        Element hash =
                hf4(
                        td.T2.powZn(csKey.sk)
                                .toBytes()
                );

        td.T1 =
                duKey.K3
                        .mul(
                                hf2(
                                        keyword,
                                        sigma
                                )
                        )
                        .powZn(hash);

        return td;
    }

    // =========================
    // Search
    // =========================

    static boolean search(
            Ciphertext ct,
            Trapdoor td,
            DOKey doKey,
            CSKey csKey) {

        Element left =
                pairing.pairing(
                        td.T1,
                        ct.W1
                );

        Element right =
                pairing.pairing(
                        g,
                        ct.W2
                );

        Element result =
                left.div(right);

        byte[] h =
                H(result);

        return Arrays.equals(
                h,
                ct.W3
        );
    }

    // =========================
    // Decrypt
    // =========================

    static void decrypt(
            Ciphertext ct,
            DUKey duKey) {

        Element z =
                hf4(
                        (ct.W0.toString()
                                + ct.W1.toString())
                                .getBytes()
                );

        Element temp =
                pairing.pairing(
                        duKey.K2,
                        ct.CR
                ).div(
                        pairing.pairing(
                                duKey.K1,
                                ct.Cp
                        )
                );

        Element recover =
                ct.C.mul(
                        temp.powZn(
                                z.invert()
                        )
                );

        System.out.println(
                "Decrypt success"
        );
    }

    // =========================
    // Benchmark
    // =========================

    public static void main(
            String[] args) {

        System.out.println(
                "Attr\tKeyGen\tEncrypt\tSearch\tDecrypt\tTotal");

        for (int attrNum = 10;
             attrNum <= 50;
             attrNum += 10) {

            setup(attrNum);

            long keyTime = 0;
            long encTime = 0;
            long searchTime = 0;
            long decTime = 0;

            int rounds = 10;

            for (int r = 0;
                 r < rounds;
                 r++) {

                List<String> attrs =
                        new ArrayList<>();

                for (int i = 0;
                     i < attrNum;
                     i++) {

                    attrs.add(
                            "ATTR" + i
                    );
                }

                long s1 =
                        System.nanoTime();

                CSKey cs =
                        csKeyGen();

                WSKey ws =
                        wsKeyGen();

                DOKey dok =
                        doKeyGen(1);

                DUKey duk =
                        duKeyGen(attrs);

                long e1 =
                        System.nanoTime();

                Element sigma =
                        keywordWarrant(
                                "2025",
                                "cloud",
                                ws
                        );

                long s2 =
                        System.nanoTime();

                Ciphertext ct =
                        encrypt(
                                "Hello",
                                "cloud",
                                sigma,
                                dok,
                                cs,
                                attrs
                        );

                long e2 =
                        System.nanoTime();

                long s3 =
                        System.nanoTime();

                Trapdoor td =
                        trapdoor(
                                "cloud",
                                sigma,
                                duk,
                                cs
                        );

                search(
                        ct,
                        td,
                        dok,
                        cs
                );

                long e3 =
                        System.nanoTime();

                long s4 =
                        System.nanoTime();

                decrypt(
                        ct,
                        duk
                );

                long e4 =
                        System.nanoTime();

                keyTime +=
                        (e1 - s1);

                encTime +=
                        (e2 - s2);

                searchTime +=
                        (e3 - s3);

                decTime +=
                        (e4 - s4);
            }

            double keyMs =
                    keyTime / 1e6 / rounds;

            double encMs =
                    encTime / 1e6 / rounds;

            double searchMs =
                    searchTime / 1e6 / rounds;

            double decMs =
                    decTime / 1e6 / rounds;

            double total =
                    keyMs
                            + encMs
                            + searchMs
                            + decMs;

            System.out.printf(
                    "%d\t%.3f\t%.3f\t%.3f\t%.3f\t%.3f\n",
                    attrNum,
                    keyMs,
                    encMs,
                    searchMs,
                    decMs,
                    total
            );
        }
    }
}
