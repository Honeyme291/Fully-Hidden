package HanYU.Yang;

import it.unisa.dia.gas.jpbc.*;
import it.unisa.dia.gas.plaf.jpbc.pairing.PairingFactory;
import it.unisa.dia.gas.plaf.jpbc.pairing.a.TypeACurveGenerator;

import java.math.BigInteger;
import java.util.*;

/**
 * JPBC Type A Simulation for:
 * KeyGen / Signcryption / Unsigncryption
 *
 * Attribute number: 10 -> 50
 *
 * Environment:
 * JPBC Type A
 *
 * NOTE:
 * This is an experimental simulation implementation for efficiency evaluation.
 * It focuses on:
 * 1. Bilinear operations
 * 2. Attribute-dependent computation
 * 3. Timing statistics
 *
 * SACF / AES / Complete LSSS reconstruction are simplified
 * because the purpose is efficiency simulation.
 */
public class Yang {

    /* =========================================================
       Global Parameters
       ========================================================= */

    static Pairing pairing;

    static Field G1;
    static Field GT;
    static Field Zr;

    static Element g;
    static Element omega;

    static Element alpha;
    static Element a;
    static Element lambda;
    static Element mu;

    static Element eggAlpha;
    static Element egwAlpha;

    static final int Z = 100;

    /* =========================================================
       Attribute Public Elements
       ========================================================= */

    static class AttributePK {
        Element hx;
        Element hxp;
    }

    static Map<String, AttributePK> attributeMap = new HashMap<>();

    /* =========================================================
       Secret Key
       ========================================================= */

    static class SecretKey {

        Element K;
        Element L1;
        Element L2;

        Map<String, Element> K1 = new HashMap<>();
        Map<String, Element> K2 = new HashMap<>();

        Map<String, int[]> spans = new HashMap<>();
    }

    /* =========================================================
       Ciphertext
       ========================================================= */

    static class Ciphertext {

        Element C;
        Element Cp1;
        Element Cp2;

        List<Element> D1 = new ArrayList<>();
        List<Element> D2 = new ArrayList<>();

        List<Element> C1 = new ArrayList<>();
        List<Element> C2 = new ArrayList<>();

        List<String> attrs = new ArrayList<>();

        Element sessionKey;
    }

    /* =========================================================
       Setup
       ========================================================= */

    public static void setup() {

        TypeACurveGenerator pg = new TypeACurveGenerator(160, 512);
        PairingParameters params = pg.generate();

        pairing = PairingFactory.getPairing(params);

        G1 = pairing.getG1();
        GT = pairing.getGT();
        Zr = pairing.getZr();

        g = G1.newRandomElement().getImmutable();
        omega = G1.newRandomElement().getImmutable();

        alpha = Zr.newRandomElement().getImmutable();
        a = Zr.newRandomElement().getImmutable();
        lambda = Zr.newRandomElement().getImmutable();
        mu = Zr.newRandomElement().getImmutable();

        eggAlpha = pairing.pairing(g, g).powZn(alpha).getImmutable();

        egwAlpha = pairing.pairing(g, omega)
                .powZn(alpha)
                .getImmutable();
    }

    /* =========================================================
       AttributeSetAdd
       ========================================================= */

    public static void attributeSetAdd(String attr) {

        AttributePK pk = new AttributePK();

        pk.hx = G1.newRandomElement().getImmutable();
        pk.hxp = G1.newRandomElement().getImmutable();

        attributeMap.put(attr, pk);
    }

    /* =========================================================
       KeyGen
       ========================================================= */

    public static SecretKey keyGen(List<String> attrs) {

        SecretKey sk = new SecretKey();

        Element t = Zr.newRandomElement().getImmutable();

        sk.K = g.powZn(alpha)
                .mul(g.powZn(a.mul(t)))
                .getImmutable();

        sk.L1 = g.powZn(t).getImmutable();

        sk.L2 = omega.powZn(t).getImmutable();

        Random rand = new Random();

        for (String attr : attrs) {

            AttributePK pk = attributeMap.get(attr);

            int ta = rand.nextInt(30);
            int tb = ta + rand.nextInt(30);

            sk.spans.put(attr, new int[]{ta, tb});

            Element k1 = pk.hx.powZn(t).getImmutable();

            Element exp1 = lambda.duplicate().pow(BigInteger.valueOf(ta));
            Element exp2 = mu.duplicate().pow(BigInteger.valueOf(Z - tb));

            Element k2 = pk.hxp.powZn(t)
                    .mul(g.powZn(exp1))
                    .mul(g.powZn(exp2))
                    .getImmutable();

            sk.K1.put(attr, k1);
            sk.K2.put(attr, k2);
        }

        return sk;
    }

    /* =========================================================
       Signcryption (Encrypt)
       ========================================================= */

    public static Ciphertext signcrypt(List<String> attrs) {

        Ciphertext ct = new Ciphertext();

        Element s = Zr.newRandomElement().getImmutable();

        ct.sessionKey = GT.newRandomElement().getImmutable();

        ct.C = ct.sessionKey.mul(
                pairing.pairing(g, omega)
                        .powZn(alpha.mul(s))
        ).getImmutable();

        ct.Cp1 = g.powZn(s).getImmutable();

        ct.Cp2 = omega.powZn(s).getImmutable();

        Random random = new Random();

        for (String attr : attrs) {

            AttributePK pk = attributeMap.get(attr);

            Element r = Zr.newRandomElement().getImmutable();

            Element gamma = Zr.newRandomElement().getImmutable();

            int ti = random.nextInt(30);
            int tj = ti + random.nextInt(30);

            Element d1 = g.powZn(r).getImmutable();

            Element d2 = omega.powZn(r).getImmutable();

            Element c1 = g.powZn(a.mul(gamma))
                    .mul(pk.hx.powZn(r).invert())
                    .getImmutable();

            Element c2 = g.powZn(a.mul(gamma))
                    .mul(pk.hxp.powZn(r).invert())
                    .getImmutable();

            ct.D1.add(d1);
            ct.D2.add(d2);

            ct.C1.add(c1);
            ct.C2.add(c2);

            ct.attrs.add(attr);
        }

        return ct;
    }

    /* =========================================================
       Unsigncryption (Decrypt)
       ========================================================= */

    public static Element unsigncrypt(SecretKey sk,
                                      Ciphertext ct,
                                      List<String> attrs) {

        Element result = pairing.pairing(ct.Cp2, sk.K);

        for (int i = 0; i < attrs.size(); i++) {

            String attr = attrs.get(i);

            Element term1 = pairing.pairing(
                    ct.C2.get(i),
                    sk.L2
            );

            Element term2 = pairing.pairing(
                    ct.D2.get(i),
                    sk.K2.get(attr)
            );

            result = result.mul(term1).mul(term2);
        }

        Element recovered = ct.C.div(result);

        return recovered;
    }

    /* =========================================================
       Main Simulation
       ========================================================= */

    public static void main(String[] args) {

        setup();

        System.out.println("==========================================");
        System.out.println(" JPBC Type A Performance Simulation ");
        System.out.println("==========================================");

        System.out.printf("%-10s %-15s %-15s %-18s %-15s\n",
                "Attrs",
                "KeyGen(ms)",
                "Signcrypt(ms)",
                "Unsigncrypt(ms)",
                "Total(ms)");

        for (int n = 10; n <= 50; n += 10) {

            List<String> attrs = new ArrayList<>();

            for (int i = 0; i < n; i++) {

                String attr = "ATTR_" + i;

                attrs.add(attr);

                if (!attributeMap.containsKey(attr)) {
                    attributeSetAdd(attr);
                }
            }

            long keygenTime = 0;
            long signTime = 0;
            long unsignTime = 0;

            int rounds = 10;

            for (int round = 0; round < rounds; round++) {

                /* =======================
                   KeyGen
                   ======================= */

                long start1 = System.nanoTime();

                SecretKey sk = keyGen(attrs);

                long end1 = System.nanoTime();

                keygenTime += (end1 - start1);

                /* =======================
                   Signcryption
                   ======================= */

                long start2 = System.nanoTime();

                Ciphertext ct = signcrypt(attrs);

                long end2 = System.nanoTime();

                signTime += (end2 - start2);

                /* =======================
                   Unsigncryption
                   ======================= */

                long start3 = System.nanoTime();

                unsigncrypt(sk, ct, attrs);

                long end3 = System.nanoTime();

                unsignTime += (end3 - start3);
            }

            double keyMs = keygenTime / 1_000_000.0 / rounds;
            double signMs = signTime / 1_000_000.0 / rounds;
            double unsignMs = unsignTime / 1_000_000.0 / rounds;

            double total = keyMs + signMs + unsignMs;

            System.out.printf("%-10d %-15.3f %-15.3f %-18.3f %-15.3f\n",
                    n,
                    keyMs,
                    signMs,
                    unsignMs,
                    total);
        }
    }
}