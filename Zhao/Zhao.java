package HanYU.Zhao;

import it.unisa.dia.gas.jpbc.*;
import it.unisa.dia.gas.plaf.jpbc.pairing.PairingFactory;
import it.unisa.dia.gas.plaf.jpbc.pairing.a.TypeACurveGenerator;

import java.util.*;

public class Zhao {

    static Pairing pairing;
    static Field G1, GT, Zr;

    static Element g;

    static Element K0, K1;
    static Element delta1, delta2;

    static Element[] mu;

    static int l = 32;

    // =========================
    // Authority
    // =========================

    static class Authority {

        Element alpha;
        Element Y;

        Map<String, Element> T = new HashMap<>();
    }

    // =========================
    // Signature Key
    // =========================

    static class SignKey {

        Map<Integer, Element> Q = new HashMap<>();
        Map<Integer, Element> Qp = new HashMap<>();
        Map<Integer, Map<String, Element>> Qpp = new HashMap<>();

        List<String> attrs;
    }

    // =========================
    // Decryption Key
    // =========================

    static class DecKey {

        Map<Integer, Element> Q = new HashMap<>();
        Map<Integer, Element> Qp = new HashMap<>();
        Map<Integer, Map<String, Element>> Qpp = new HashMap<>();

        List<String> attrs;
    }

    // =========================
    // Ciphertext
    // =========================

    static class Ciphertext {

        Element C1, C2, C4;

        byte[] C3;

        Element sigma1;
        Element sigma2;
        String sigma3;
        Element sigma4;
    }

    // =========================
    // Hash
    // =========================

    static Element H3(Element e) {
        return Zr.newElement()
                .setFromHash(e.toBytes(), 0, e.toBytes().length)
                .getImmutable();
    }

    static Element H4(String s) {
        return Zr.newElement()
                .setFromHash(s.getBytes(), 0, s.length())
                .getImmutable();
    }

    // =========================
    // Setup
    // =========================

    static void setup() {

        TypeACurveGenerator pg =
                new TypeACurveGenerator(160, 512);

        PairingParameters params =
                pg.generate();

        pairing =
                PairingFactory.getPairing(params);

        G1 = pairing.getG1();
        GT = pairing.getGT();
        Zr = pairing.getZr();

        g = G1.newRandomElement().getImmutable();

        K0 = G1.newRandomElement().getImmutable();
        K1 = G1.newRandomElement().getImmutable();

        delta1 = G1.newRandomElement().getImmutable();
        delta2 = G1.newRandomElement().getImmutable();

        mu = new Element[l + 1];

        for (int i = 0; i <= l; i++) {
            mu[i] = G1.newRandomElement().getImmutable();
        }
    }

    // =========================
    // Authority Setup
    // =========================

    static Authority authoritySetup(
            List<String> attrs) {

        Authority aa = new Authority();

        aa.alpha =
                Zr.newRandomElement().getImmutable();

        aa.Y =
                pairing.pairing(g, g)
                        .powZn(aa.alpha)
                        .getImmutable();

        for (String att : attrs) {

            aa.T.put(
                    att,
                    G1.newRandomElement().getImmutable()
            );
        }

        return aa;
    }

    // =========================
    // SignKeyGen
    // =========================

    static SignKey signKeyGen(
            Authority aa,
            List<String> attrs) {

        SignKey sk = new SignKey();

        for (int i = 0; i < attrs.size(); i++) {

            Element lambda =
                    Zr.newRandomElement();

            Element r =
                    Zr.newRandomElement();

            String att = attrs.get(i);

            Element Q =
                    g.powZn(lambda)
                            .mul(
                                    K0.mul(aa.T.get(att))
                                            .powZn(r)
                            );

            Element Qp =
                    g.powZn(r);

            Map<String, Element> qpp =
                    new HashMap<>();

            for (String other : attrs) {

                if (!other.equals(att)) {

                    qpp.put(
                            other,
                            aa.T.get(other)
                                    .powZn(r)
                    );
                }
            }

            sk.Q.put(i, Q.getImmutable());
            sk.Qp.put(i, Qp.getImmutable());
            sk.Qpp.put(i, qpp);
        }

        sk.attrs = attrs;

        return sk;
    }

    // =========================
    // DecKeyGen
    // =========================

    static DecKey decKeyGen(
            Authority aa,
            List<String> attrs) {

        DecKey dk = new DecKey();

        for (int i = 0; i < attrs.size(); i++) {

            Element lambda =
                    Zr.newRandomElement();

            Element eta =
                    Zr.newRandomElement();

            String att = attrs.get(i);

            Element Q =
                    g.powZn(lambda)
                            .mul(
                                    K1.mul(aa.T.get(att))
                                            .powZn(eta)
                            );

            Element Qp =
                    g.powZn(eta);

            Map<String, Element> qpp =
                    new HashMap<>();

            for (String other : attrs) {

                if (!other.equals(att)) {

                    qpp.put(
                            other,
                            aa.T.get(other)
                                    .powZn(eta)
                    );
                }
            }

            dk.Q.put(i, Q.getImmutable());
            dk.Qp.put(i, Qp.getImmutable());
            dk.Qpp.put(i, qpp);
        }

        dk.attrs = attrs;

        return dk;
    }

    // =========================
    // Signcrypt
    // =========================

    static Ciphertext signcrypt(
            String message,
            List<Authority> authorities,
            List<SignKey> signKeys,
            List<String> Rs,
            List<String> Re) {

        Ciphertext ct = new Ciphertext();

        Element beta =
                Zr.newRandomElement();

        Element varsigma =
                Zr.newRandomElement();

        Element xi =
                Zr.newRandomElement();

        ct.C1 =
                g.powZn(beta).getImmutable();

        Element temp =
                K1.duplicate();

        for (Authority aa : authorities) {

            for (String att : Re) {

                if (aa.T.containsKey(att)) {

                    temp =
                            temp.mul(
                                    aa.T.get(att)
                            );
                }
            }
        }

        ct.C2 =
                temp.powZn(beta).getImmutable();

        ct.sigma1 =
                g.powZn(beta.mul(varsigma));

        Element sigma2 =
                g.powZn(xi);

        for (SignKey sk : signKeys) {

            for (Element e : sk.Qp.values()) {

                sigma2 = sigma2.mul(e);
            }
        }

        ct.sigma2 = sigma2.getImmutable();

        Element Lambda =
                GT.newOneElement();

        for (Authority aa : authorities) {

            Lambda =
                    Lambda.mul(
                            aa.Y.powZn(beta)
                    );
        }

        ct.sigma3 = "pi";

        byte[] hash =
                Lambda.toBytes();

        byte[] msg =
                message.getBytes();

        byte[] c3 =
                new byte[msg.length];

        for (int i = 0; i < msg.length; i++) {

            c3[i] =
                    (byte)(msg[i] ^
                            hash[i % hash.length]);
        }

        ct.C3 = c3;

        Element muValue =
                H3(ct.C1);

        ct.C4 =
                delta1.powZn(muValue)
                        .mul(delta2)
                        .powZn(beta)
                        .getImmutable();

        Element sigma4 =
                G1.newOneElement();

        for (SignKey sk : signKeys) {

            for (Element e : sk.Q.values()) {

                sigma4 = sigma4.mul(e);
            }
        }

        sigma4 =
                sigma4.mul(
                        K0.powZn(xi)
                );

        sigma4 =
                sigma4.mul(
                        mu[0].powZn(beta)
                );

        sigma4 =
                sigma4.mul(
                        ct.C4.powZn(
                                H4("theta")
                                        .mul(varsigma)
                        )
                );

        ct.sigma4 =
                sigma4.getImmutable();

        return ct;
    }

    // =========================
    // Verify + Decrypt
    // =========================

    static void unsigncrypt(
            Ciphertext ct,
            List<Authority> authorities,
            List<DecKey> decKeys) {

        Element left =
                pairing.pairing(
                        ct.sigma4,
                        g
                );

        Element right =
                GT.newOneElement();

        for (Authority aa : authorities) {

            right = right.mul(aa.Y);
        }

        right =
                right.mul(
                        pairing.pairing(
                                K0,
                                ct.sigma2
                        )
                );

        right =
                right.mul(
                        pairing.pairing(
                                mu[0],
                                ct.C1
                        )
                );

        Element theta =
                H4("theta");

        Element muValue =
                H3(ct.C1);

        Element temp =
                delta1.powZn(muValue)
                        .mul(delta2)
                        .powZn(theta);

        right =
                right.mul(
                        pairing.pairing(
                                temp,
                                ct.sigma1
                        )
                );

        boolean verify =
                left.isEqual(right);

        if (!verify) {

            System.out.println(
                    "Verify Failed"
            );

            return;
        }

        Element E1 =
                G1.newOneElement();

        Element E2 =
                G1.newOneElement();

        for (DecKey dk : decKeys) {

            for (Element e : dk.Q.values()) {

                E1 = E1.mul(e);
            }

            for (Element e : dk.Qp.values()) {

                E2 = E2.mul(e);
            }
        }

        Element Lambda =
                pairing.pairing(
                        ct.C1,
                        E1
                ).div(
                        pairing.pairing(
                                ct.C2,
                                E2
                        )
                );

        byte[] hash =
                Lambda.toBytes();

        byte[] msg =
                new byte[ct.C3.length];

        for (int i = 0; i < msg.length; i++) {

            msg[i] =
                    (byte)(ct.C3[i] ^
                            hash[i % hash.length]);
        }

        String recover =
                new String(msg);

        System.out.println(
                "Recover: " + recover
        );
    }

    // =========================
    // Benchmark
    // =========================

    public static void main(String[] args) {

        setup();

        System.out.println(
                "Attr\tKeyGen\tSigncrypt\tUnsigncrypt\tTotal");

        for (int attrNum = 10;
             attrNum <= 50;
             attrNum += 10) {

            List<String> attrs =
                    new ArrayList<>();

            for (int i = 0; i < attrNum; i++) {

                attrs.add("ATTR" + i);
            }

            int rounds = 10;

            long keyTime = 0;
            long signTime = 0;
            long unsignTime = 0;

            for (int r = 0; r < rounds; r++) {

                long s1 =
                        System.nanoTime();

                Authority aa =
                        authoritySetup(attrs);

                SignKey sk =
                        signKeyGen(aa, attrs);

                DecKey dk =
                        decKeyGen(aa, attrs);

                long e1 =
                        System.nanoTime();

                List<Authority> aas =
                        Arrays.asList(aa);

                List<SignKey> sks =
                        Arrays.asList(sk);

                List<DecKey> dks =
                        Arrays.asList(dk);

                long s2 =
                        System.nanoTime();

                Ciphertext ct =
                        signcrypt(
                                "Hello",
                                aas,
                                sks,
                                attrs,
                                attrs
                        );

                long e2 =
                        System.nanoTime();

                long s3 =
                        System.nanoTime();

                unsigncrypt(
                        ct,
                        aas,
                        dks
                );

                long e3 =
                        System.nanoTime();

                keyTime += (e1 - s1);
                signTime += (e2 - s2);
                unsignTime += (e3 - s3);
            }

            double keyMs =
                    keyTime / 1e6 / rounds;

            double signMs =
                    signTime / 1e6 / rounds;

            double unsignMs =
                    unsignTime / 1e6 / rounds;

            double total =
                    keyMs + signMs + unsignMs;

            System.out.printf(
                    "%d\t%.3f\t%.3f\t%.3f\t%.3f\n",
                    attrNum,
                    keyMs,
                    signMs,
                    unsignMs,
                    total
            );
        }
    }
}