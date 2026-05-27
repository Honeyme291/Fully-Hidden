package HanYU.Ours;

import it.unisa.dia.gas.jpbc.*;
import it.unisa.dia.gas.plaf.jpbc.pairing.PairingFactory;
import it.unisa.dia.gas.plaf.jpbc.pairing.a.TypeACurveGenerator;

import java.util.*;

public class Ours {

    static Pairing pairing;
    static Field G1, GT, Zr;

    static Element g;
    static Element gamma;
    static Element alphaE;
    static Element alphaS;

    static Element eggAlphaE;
    static Element eggAlphaS;

    static int messageLength = 32;

    // =========================
    // Hash Functions
    // =========================

    static Element H1(String s) {
        return G1.newElement().setFromHash(s.getBytes(), 0, s.length()).getImmutable();
    }

    static Element H2(String s) {
        return Zr.newElement().setFromHash(s.getBytes(), 0, s.length()).getImmutable();
    }

    static byte[] H3(String s) {
        return s.getBytes();
    }

    // =========================
    // User Secret Key
    // =========================

    static class SecretKey {

        Element KE;
        Element K0E;
        Map<String, Element> KAttE = new HashMap<>();

        Element KS;
        Element K0S;
        Map<String, Element> KAttS = new HashMap<>();

        Set<String> attrs;
    }

    // =========================
    // Ciphertext
    // =========================

    static class Ciphertext {

        Element C1;
        Element C2;

        Map<Integer, Element> C3 = new HashMap<>();
        Map<Integer, Element> C4 = new HashMap<>();

        Map<Integer, Element> sigma1 = new HashMap<>();

        Element sigma2;

        List<String> policyE;
        List<String> policyS;
    }

    // =========================
    // Setup
    // =========================

    static void setup() {

        TypeACurveGenerator pg = new TypeACurveGenerator(160, 512);
        PairingParameters params = pg.generate();

        pairing = PairingFactory.getPairing(params);

        G1 = pairing.getG1();
        GT = pairing.getGT();
        Zr = pairing.getZr();

        g = G1.newRandomElement().getImmutable();

        gamma = Zr.newRandomElement().getImmutable();
        alphaE = Zr.newRandomElement().getImmutable();
        alphaS = Zr.newRandomElement().getImmutable();

        eggAlphaE = pairing.pairing(g, g).powZn(alphaE).getImmutable();
        eggAlphaS = pairing.pairing(g, g).powZn(alphaS).getImmutable();
    }

    // =========================
    // KeyGen
    // =========================

    static SecretKey keyGen(Set<String> attrs) {

        SecretKey sk = new SecretKey();

        Element zE = Zr.newRandomElement().getImmutable();
        Element zS = Zr.newRandomElement().getImmutable();

        sk.KE = g.powZn(alphaE.add(gamma.mul(zE))).getImmutable();
        sk.K0E = g.powZn(zE).getImmutable();

        sk.KS = g.powZn(alphaS.add(gamma.mul(zS))).getImmutable();
        sk.K0S = g.powZn(zS).getImmutable();

        for (String att : attrs) {

            Element h = H1(att);

            sk.KAttE.put(att, h.powZn(zE).getImmutable());
            sk.KAttS.put(att, h.powZn(zS).getImmutable());
        }

        sk.attrs = attrs;

        return sk;
    }

    // =========================
    // Signcryption
    // =========================

    static Ciphertext signcrypt(SecretKey sk,
                                String message,
                                List<String> policyE,
                                List<String> policyS) {

        Ciphertext ct = new Ciphertext();

        Element r = Zr.newRandomElement().getImmutable();

        Element m = GT.newRandomElement().getImmutable();

        ct.C1 = m.mul(eggAlphaE.powZn(r)).getImmutable();

        ct.C2 = g.powZn(r).getImmutable();

        int lE = policyE.size();

        for (int i = 0; i < lE; i++) {

            Element lambda = Zr.newRandomElement();

            Element ri = Zr.newRandomElement();

            String rho = policyE.get(i);

            Element c3 = g.powZn(gamma.mul(lambda))
                    .mul(H1(rho).powZn(ri).invert());

            Element c4 = g.powZn(ri);

            ct.C3.put(i, c3.getImmutable());
            ct.C4.put(i, c4.getImmutable());
        }

        Element Ymu = G1.newOneElement();

        for (int i = 0; i < lE; i++) {
            Ymu = Ymu.mul(ct.C4.get(i));
        }

        int lS = policyS.size();

        for (int i = 0; i < lS; i++) {

            Element vi = Zr.newRandomElement();
            Element wi = Zr.newRandomElement();

            Element sigma1 =
                    sk.K0S.powZn(vi).mul(g.powZn(wi));

            ct.sigma1.put(i, sigma1.getImmutable());
        }

        Element sigma2 = sk.KS.duplicate();

        for (String att : policyS) {

            if (sk.KAttS.containsKey(att)) {

                sigma2 = sigma2.mul(sk.KAttS.get(att));
            }
        }

        sigma2 = sigma2.mul(Ymu.powZn(r));

        ct.sigma2 = sigma2.getImmutable();

        ct.policyE = policyE;
        ct.policyS = policyS;

        return ct;
    }

    // =========================
    // Unsigncryption
    // =========================

    static void unsigncrypt(SecretKey sk,
                            Ciphertext ct) {

        Element denominator = GT.newOneElement();

        for (int i = 0; i < ct.policyE.size(); i++) {

            String rho = ct.policyE.get(i);

            if (!sk.KAttE.containsKey(rho))
                continue;

            Element p1 =
                    pairing.pairing(sk.K0E, ct.C3.get(i));

            Element p2 =
                    pairing.pairing(sk.KAttE.get(rho),
                            ct.C4.get(i));

            denominator =
                    denominator.mul(p1.mul(p2));
        }

        Element numerator =
                pairing.pairing(sk.KE, ct.C2);

        Element D = numerator.div(denominator);

        Element mRecover = ct.C1.div(D);

        // verification

        Element left =
                pairing.pairing(g, ct.sigma2);

        Element right =
                eggAlphaS.duplicate();

        for (int i = 0; i < ct.policyS.size(); i++) {

            String rho = ct.policyS.get(i);

            Element lambda = Zr.newRandomElement();

            Element temp =
                    pairing.pairing(
                            g.powZn(gamma.mul(lambda))
                                    .mul(H1(rho)),
                            ct.sigma1.get(i));

            right = right.mul(temp);
        }

        boolean ok = left.isEqual(right);

        if (!ok) {
            System.out.println("Verification failed.");
        }
    }

    // =========================
    // Main Benchmark
    // =========================

    public static void main(String[] args) {

        setup();

        System.out.println("AttrNum\tKeyGen(ms)\tSigncrypt(ms)\tUnsigncrypt(ms)\tTotal(ms)");

        for (int attrNum = 10; attrNum <= 50; attrNum += 10) {

            Set<String> attrs = new HashSet<>();

            for (int i = 0; i < attrNum; i++) {
                attrs.add("ATTR" + i);
            }

            List<String> policyE = new ArrayList<>(attrs);
            List<String> policyS = new ArrayList<>(attrs);

            int testRounds = 20;

            long keyGenTime = 0;
            long signTime = 0;
            long unsignTime = 0;

            for (int t = 0; t < testRounds; t++) {

                long start1 = System.nanoTime();

                SecretKey sk = keyGen(attrs);

                long end1 = System.nanoTime();

                long start2 = System.nanoTime();

                Ciphertext ct =
                        signcrypt(sk,
                                "hello",
                                policyE,
                                policyS);

                long end2 = System.nanoTime();

                long start3 = System.nanoTime();

                unsigncrypt(sk, ct);

                long end3 = System.nanoTime();

                keyGenTime += (end1 - start1);
                signTime += (end2 - start2);
                unsignTime += (end3 - start3);
            }

            double keyMs =
                    keyGenTime / 1e6 / testRounds;

            double signMs =
                    signTime / 1e6 / testRounds;

            double unsignMs =
                    unsignTime / 1e6 / testRounds;

            double total =
                    keyMs + signMs + unsignMs;

            System.out.printf(
                    "%d\t\t%.3f\t\t%.3f\t\t%.3f\t\t%.3f\n",
                    attrNum,
                    keyMs,
                    signMs,
                    unsignMs,
                    total
            );
        }
    }
}