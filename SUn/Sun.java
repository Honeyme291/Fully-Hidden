package HanYU.SUn;

import it.unisa.dia.gas.jpbc.*;
import it.unisa.dia.gas.plaf.jpbc.pairing.PairingFactory;
import it.unisa.dia.gas.plaf.jpbc.pairing.a.TypeACurveGenerator;

import java.math.BigInteger;
import java.security.MessageDigest;
import java.util.*;

public class Sun {

    // ================================
    // System Parameters
    // ================================

    static Pairing pairing;
    static Field G1;
    static Field GT;
    static Field Zr;

    static Element g;
    static Element Z;
    static Element Y;

    static Element[] g_i;

    static Element[] l_i;
    static Element l0;

    static BigInteger p;

    static int VECTOR_SIZE = 50;

    static class MSK {
        Element alpha;
        Element beta;
        Element[] tau;
    }

    static MSK msk = new MSK();

    // ================================
    // User Secret Key
    // ================================

    static class UserSK {

        int id;

        int[] uVector;

        Element sk1;
        Element sk2;
        Element sk3;

        Element sk1_p;
        Element sk2_p;
        Element sk3_p;
    }

    // ================================
    // Ciphertext
    // ================================

    static class Ciphertext {

        Element C;
        Element Cp;
        Element Cpp;

        Element C0;

        Element[] Ci;
        Element[] gamma_i;

        Element[] hatCj;
    }

    // ================================
    // Trapdoor
    // ================================

    static class Trapdoor {

        int[] uVector;

        Element td1;
        Element td2;
        Element td3;
    }

    // ================================
    // Hash Functions
    // ================================

    static Element hashToZr(String s) throws Exception {

        MessageDigest md = MessageDigest.getInstance("SHA-256");

        byte[] digest = md.digest(s.getBytes());

        return Zr.newElementFromHash(digest, 0, digest.length).getImmutable();
    }

    // ================================
    // Setup
    // ================================

    static void setup(int n) {

        TypeACurveGenerator pg =
                new TypeACurveGenerator(160, 512);

        PairingParameters params = pg.generate();

        pairing = PairingFactory.getPairing(params);

        G1 = pairing.getG1();
        GT = pairing.getGT();
        Zr = pairing.getZr();

        g = G1.newRandomElement().getImmutable();

        msk.alpha = Zr.newRandomElement().getImmutable();
        msk.beta = Zr.newRandomElement().getImmutable();

        msk.tau = new Element[n];

        g_i = new Element[n];

        for(int i=0;i<n;i++){

            msk.tau[i] = Zr.newRandomElement().getImmutable();

            g_i[i] = g.powZn(msk.tau[i]).getImmutable();
        }

        Z = pairing.pairing(g,g)
                .powZn(msk.alpha)
                .getImmutable();

        Y = pairing.pairing(g,g)
                .powZn(msk.alpha.mul(msk.beta))
                .getImmutable();

        l0 = G1.newRandomElement().getImmutable();

        l_i = new Element[n];

        for(int i=0;i<n;i++){

            l_i[i] = G1.newRandomElement().getImmutable();
        }
    }

    // ================================
    // Vectorization
    // ================================

    static int[] vectorize(Set<Integer> attrs, int n){

        int[] vec = new int[n];

        for(Integer a : attrs){

            vec[a] = 1;
        }

        return vec;
    }

    // ================================
    // KeyGen
    // ================================

    static UserSK keyGen(Set<Integer> attrs, int n){

        UserSK sk = new UserSK();

        sk.uVector = vectorize(attrs,n);

        Element s =
                Zr.newRandomElement().getImmutable();

        Element sp =
                Zr.newRandomElement().getImmutable();

        Element sum =
                Zr.newZeroElement();

        for(int i=0;i<n;i++){

            if(sk.uVector[i]==1){

                sum.add(msk.tau[i]);
            }
        }

        sk.sk1 =
                g.powZn(msk.alpha)
                        .mul(g.powZn(s.mul(sum)))
                        .getImmutable();

        sk.sk2 =
                g.powZn(s).getImmutable();

        sk.sk3 =
                g.powZn(
                        Zr.newRandomElement()
                ).getImmutable();

        sk.sk1_p =
                g.powZn(
                        msk.alpha.mul(msk.beta)
                ).mul(
                        g.powZn(sp.mul(sum))
                ).getImmutable();

        sk.sk2_p =
                g.powZn(sp).getImmutable();

        sk.sk3_p =
                g.powZn(
                        Zr.newRandomElement()
                ).getImmutable();

        return sk;
    }

    // ================================
    // Offline Encryption
    // ================================

    static class OfflineCT {

        Element delta;

        Element[] eta;

        Element C0;

        Element[] Ci;

        Element hatC0;

        Element[] hatCj;
    }

    static OfflineCT offEnc(int n){

        OfflineCT off = new OfflineCT();

        off.delta =
                Zr.newRandomElement().getImmutable();

        off.eta = new Element[n];

        off.Ci = new Element[n];

        off.hatCj = new Element[n];

        off.C0 =
                g.powZn(off.delta).getImmutable();

        for(int i=0;i<n;i++){

            off.eta[i] =
                    Zr.newRandomElement().getImmutable();

            off.Ci[i] =
                    g.powZn(
                            off.delta.mul(msk.tau[i])
                    ).mul(
                            g.powZn(off.eta[i].negate())
                    ).getImmutable();
        }

        off.hatC0 =
                l0.powZn(off.delta).getImmutable();

        for(int i=0;i<n;i++){

            off.hatCj[i] =
                    l_i[i].powZn(off.delta)
                            .getImmutable();
        }

        return off;
    }

    // ================================
    // Online Encryption
    // ================================

    static Ciphertext onEnc(
            OfflineCT off,
            String keyword,
            String message,
            Set<Integer> policyAttrs,
            int n
    ) throws Exception {

        Ciphertext ct = new Ciphertext();

        int[] v = vectorize(policyAttrs,n);

        Element theta =
                Zr.newRandomElement().getImmutable();

        Element Hw =
                hashToZr(keyword);

        Element M =
                GT.newRandomElement().getImmutable();

        ct.C =
                M.mul(
                        Z.powZn(off.delta)
                ).getImmutable();

        ct.Cp =
                Y.powZn(
                        Hw.mul(off.delta)
                ).getImmutable();

        ct.C0 = off.C0;

        ct.Ci = off.Ci;

        ct.gamma_i = new Element[n];

        for(int i=0;i<n;i++){

            Element vi =
                    Zr.newElement(v[i]);

            ct.gamma_i[i] =
                    off.eta[i]
                            .add(
                                    vi.mul(theta)
                            ).getImmutable();
        }

        ct.Cpp =
                off.hatC0.getImmutable();

        return ct;
    }

    // ================================
    // Trapdoor
    // ================================

    static Trapdoor trapGen(
            UserSK usk,
            String keyword
    ) throws Exception {

        Trapdoor td = new Trapdoor();

        td.uVector = usk.uVector;

        Element Hq =
                hashToZr(keyword);

        td.td1 =
                usk.sk1_p.powZn(Hq)
                        .getImmutable();

        td.td2 =
                usk.sk2_p.powZn(Hq)
                        .getImmutable();

        td.td3 =
                usk.sk3_p.powZn(Hq)
                        .getImmutable();

        return td;
    }

    // ================================
    // Search
    // ================================

    static boolean search(
            Ciphertext ct,
            Trapdoor td,
            int n
    ){

        Element C0p =
                G1.newOneElement();

        for(int i=0;i<n;i++){

            if(td.uVector[i]==1){

                C0p = C0p.mul(
                        ct.Ci[i].powZn(
                                Zr.newElement(
                                        td.uVector[i]
                                )
                        )
                );
            }
        }

        Element left =
                ct.Cp;

        Element right =
                pairing.pairing(
                        ct.C0,
                        td.td1
                ).div(
                        pairing.pairing(
                                C0p,
                                td.td2
                        )
                );

        return left.isEqual(right);
    }

    // ================================
    // Decrypt
    // ================================

    static void decrypt(
            Ciphertext ct,
            UserSK usk
    ){

        Element M =
                ct.C.div(
                        pairing.pairing(
                                ct.C0,
                                usk.sk1
                        ).div(
                                pairing.pairing(
                                        ct.C0,
                                        usk.sk2
                                )
                        )
                );

    }

    // ================================
    // Main Benchmark
    // ================================

    public static void main(String[] args)
            throws Exception {

        System.out.println(
                "Attr\tKeyGen\tEnc\tSearch+Dec\tTotal"
        );

        for(int attrNum=10;
            attrNum<=50;
            attrNum+=10){

            setup(attrNum);

            Set<Integer> attrs =
                    new HashSet<>();

            for(int i=0;i<attrNum;i++){

                attrs.add(i);
            }

            long keyTime = 0;
            long encTime = 0;
            long decTime = 0;

            for(int round=0;
                round<10;
                round++){

                // ====================
                // KeyGen
                // ====================

                long s1 =
                        System.nanoTime();

                UserSK sk =
                        keyGen(attrs,attrNum);

                long e1 =
                        System.nanoTime();

                keyTime += (e1-s1);

                // ====================
                // Encryption
                // ====================

                long s2 =
                        System.nanoTime();

                OfflineCT off =
                        offEnc(attrNum);

                Ciphertext ct =
                        onEnc(
                                off,
                                "keyword",
                                "message",
                                attrs,
                                attrNum
                        );

                long e2 =
                        System.nanoTime();

                encTime += (e2-s2);

                // ====================
                // Trapdoor + Search
                // ====================

                long s3 =
                        System.nanoTime();

                Trapdoor td =
                        trapGen(sk,"keyword");

                search(ct,td,attrNum);

                decrypt(ct,sk);

                long e3 =
                        System.nanoTime();

                decTime += (e3-s3);
            }

            double keyMs =
                    keyTime/1e6/10.0;

            double encMs =
                    encTime/1e6/10.0;

            double decMs =
                    decTime/1e6/10.0;

            double total =
                    keyMs+encMs+decMs;

            System.out.printf(
                    "%d\t%.2f\t%.2f\t%.2f\t%.2f\n",
                    attrNum,
                    keyMs,
                    encMs,
                    decMs,
                    total
            );
        }
    }
}
