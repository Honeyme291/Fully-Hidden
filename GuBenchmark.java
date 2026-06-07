package Rao;

import it.unisa.dia.gas.jpbc.*;
import it.unisa.dia.gas.plaf.jpbc.pairing.PairingFactory;
import java.security.MessageDigest;
import java.security.SecureRandom;
import java.util.*;

public class ABSCBenchmark {

    private Pairing pairing;
    private SecureRandom random;
    private MessageDigest sha256;

    // 系统参数
    public static class SystemParams {
        Pairing pairing;
        Element g_T, g, h, h1, h2, h3;
        Element[] g_i; // g1 to g5
        Element g_alpha; // 主密钥
        Element z1, z2, z3;

        public SystemParams(Pairing pairing) {
            this.pairing = pairing;
            this.g_i = new Element[5];
        }
    }

    // 签名密钥
    public static class SigningKey {
        Set<String> attributes;
        Element S01, S02;
        Map<String, Element> S_x;

        public SigningKey() {
            attributes = new HashSet<>();
            S_x = new HashMap<>();
        }
    }

    // 解密密钥
    public static class DecryptionKey {
        Set<String> attributes;
        Element D01, D02, D03;
        Map<String, Element> D_y;

        public DecryptionKey() {
            attributes = new HashSet<>();
            D_y = new HashMap<>();
        }
    }

    // 密文
    public static class Ciphertext {
        byte[] ct;
        Element sigma;
        Map<Integer, Element> sigma_i;
        Element E;
        Map<Integer, EncComponent> E_i;
        Element E0;
        Element eta;
        byte[] tag_e;

        public Ciphertext() {
            sigma_i = new HashMap<>();
            E_i = new HashMap<>();
        }
    }

    public static class EncComponent {
        Element E_i1, E_i2;
    }

    public ABSCBenchmark() {
        try {
            pairing = PairingFactory.getPairing("E:/java program/Han/src/Belgiud/a.properties");
            PairingFactory.getInstance().setUsePBCWhenPossible(true);
            random = new SecureRandom();
            sha256 = MessageDigest.getInstance("SHA-256");
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    /**
     * Setup - 系统初始化
     */
    public SystemParams setup() {
        SystemParams params = new SystemParams(pairing);

        // 选择随机数
        Element alpha = pairing.getZr().newRandomElement().getImmutable();
        params.z1 = pairing.getZr().newRandomElement().getImmutable();
        params.z2 = pairing.getZr().newRandomElement().getImmutable();
        params.z3 = pairing.getZr().newRandomElement().getImmutable();

        // 选择生成元
        params.g = pairing.getG1().newRandomElement().getImmutable();
        params.h = pairing.getG1().newRandomElement().getImmutable();

        for (int i = 0; i < 5; i++) {
            params.g_i[i] = pairing.getG1().newRandomElement().getImmutable();
        }

        // 计算公钥组件
        params.g_T = pairing.pairing(params.g, params.g).powZn(alpha).getImmutable();
        params.g_alpha = params.g.powZn(alpha).getImmutable();
        params.h1 = params.g.powZn(params.z1).getImmutable();
        params.h2 = params.g.powZn(params.z2).getImmutable();
        params.h3 = params.g.powZn(params.z3).getImmutable();

        return params;
    }

    /**
     * H1: Hash to G1 - 将属性哈希到群元素
     */
    private Element H1(String attribute, SystemParams params) {
        byte[] hash = sha256.digest(("H1_" + attribute).getBytes());
        return params.pairing.getG1().newElementFromHash(hash, 0, hash.length).getImmutable();
    }

    /**
     * H2: Hash to G1
     */
    private Element H2(String attribute, SystemParams params) {
        byte[] hash = sha256.digest(("H2_" + attribute).getBytes());
        return params.pairing.getG1().newElementFromHash(hash, 0, hash.length).getImmutable();
    }

    /**
     * H3: Hash GT to Zr
     */
    private Element H3(Element gt_element) {
        byte[] hash = sha256.digest(gt_element.toBytes());
        return pairing.getZr().newElementFromHash(hash, 0, hash.length).getImmutable();
    }

    /**
     * H6: Hash to Zr
     */
    private Element H6(byte[] data) {
        byte[] hash = sha256.digest(data);
        return pairing.getZr().newElementFromHash(hash, 0, hash.length).getImmutable();
    }

    /**
     * H7: Hash to Zr
     */
    private Element H7(byte[] data) {
        byte[] hash = sha256.digest(data);
        return pairing.getZr().newElementFromHash(hash, 0, hash.length).getImmutable();
    }

    /**
     * KDF - 密钥派生函数
     */
    private byte[] KDF(Element gt_element, int length) {
        byte[] input = gt_element.toBytes();
        byte[] output = new byte[length / 8];
        byte[] hash = sha256.digest(input);
        System.arraycopy(hash, 0, output, 0, Math.min(hash.length, output.length));
        return output;
    }

    /**
     * 生成签名密钥
     */
    public SigningKey keyGenSigning(SystemParams params, Set<String> attributes) {
        SigningKey sk = new SigningKey();
        sk.attributes = new HashSet<>(attributes);

        Element r_s = pairing.getZr().newRandomElement().getImmutable();

        // S01 = g^alpha * h^r_s
        sk.S01 = params.g_alpha.duplicate().mul(params.h.powZn(r_s)).getImmutable();

        // S02 = g^r_s
        sk.S02 = params.g.powZn(r_s).getImmutable();

        // S_x = H1(x)^r_s for each attribute x
        for (String attr : attributes) {
            Element S_x = H1(attr, params).powZn(r_s).getImmutable();
            sk.S_x.put(attr, S_x);
        }

        return sk;
    }

    /**
     * 生成解密密钥
     */
    public DecryptionKey keyGenDecryption(SystemParams params, Set<String> attributes) {
        DecryptionKey dk = new DecryptionKey();
        dk.attributes = new HashSet<>(attributes);

        Element r_d = pairing.getZr().newRandomElement().getImmutable();

        // D01 = g^alpha * h^r_d
        dk.D01 = params.g_alpha.duplicate().mul(params.h.powZn(r_d)).getImmutable();

        // D02 = h1^r_d
        dk.D02 = params.h1.powZn(r_d).getImmutable();

        // D03 = h2^r_d
        dk.D03 = params.h2.powZn(r_d).getImmutable();

        // D_y = H2(y)^r_d for each attribute y
        for (String attr : attributes) {
            Element D_y = H2(attr, params).powZn(r_d).getImmutable();
            dk.D_y.put(attr, D_y);
        }

        return dk;
    }

    /**
     * Signcrypt - 签密算法（简化版，不含访问结构）
     */
    public Ciphertext signcrypt(SystemParams params, byte[] message, SigningKey sk,
                                Set<String> encPolicy) {
        Ciphertext ct = new Ciphertext();

        // 选择随机数 theta
        Element theta = pairing.getZr().newRandomElement().getImmutable();

        // 计算 g_T^theta
        Element g_T_theta = params.g_T.powZn(theta).getImmutable();

        // 加密消息: ct = msg XOR KDF(g_T^theta)
        byte[] key = KDF(g_T_theta, message.length * 8);
        ct.ct = new byte[message.length];
        for (int i = 0; i < message.length; i++) {
            ct.ct[i] = (byte) (message[i] ^ key[i]);
        }

        // 计算 gamma = H3(g_T^theta)
        Element gamma = H3(g_T_theta);
        Element gamma_inv = gamma.duplicate().invert().getImmutable();

        // 生成标签
        ct.tag_e = sha256.digest(ct.ct);

        // 重随机化签名密钥
        Element r_prime = pairing.getZr().newRandomElement().getImmutable();
        Element S01_tilde = sk.S01.duplicate().mul(params.h.powZn(r_prime)).getImmutable();
        Element S02_tilde = sk.S02.duplicate().mul(params.g.powZn(r_prime)).getImmutable();

        // 计算签名组件
        Element o1 = pairing.getZr().newRandomElement().getImmutable();
        Element o2 = H6(ct.ct);

        // sigma = S01^(1/gamma) * (g1^o2 * g2)^theta * ...
        ct.sigma = S01_tilde.powZn(gamma_inv).getImmutable();
        Element temp = params.g_i[0].powZn(o2).mul(params.g_i[1]).powZn(theta);
        ct.sigma = ct.sigma.mul(temp).getImmutable();

        // 对每个属性计算 sigma_i
        int i = 0;
        for (String attr : sk.attributes) {
            Element a_i = pairing.getZr().newRandomElement().getImmutable();
            Element b_i = pairing.getZr().newRandomElement().getImmutable();

            Element S_x = sk.S_x.get(attr);
            Element sigma_component = S_x.powZn(a_i.duplicate().mul(gamma_inv));
            sigma_component = sigma_component.mul(H1(attr, params).powZn(o1.duplicate().mul(b_i)));

            ct.sigma = ct.sigma.mul(sigma_component).getImmutable();

            Element sigma_i = S02_tilde.powZn(a_i.duplicate().mul(gamma_inv))
                    .mul(params.g.powZn(o1.duplicate().mul(b_i)));
            ct.sigma_i.put(i, sigma_i.getImmutable());
            i++;
        }

        // 加密组件
        ct.E = params.g.powZn(theta).getImmutable();

        // 对每个加密策略属性
        int j = 0;
        for (String attr : encPolicy) {
            Element theta_i = pairing.getZr().newRandomElement().getImmutable();

            EncComponent ec = new EncComponent();
            ec.E_i1 = params.g.powZn(theta_i).getImmutable();
            ec.E_i2 = params.h.powZn(theta).mul(H2(attr, params).powZn(theta_i)).getImmutable();

            ct.E_i.put(j, ec);
            j++;
        }

        // E0 组件
        ct.eta = pairing.getZr().newRandomElement().getImmutable();
        Element xi = H7(ct.ct);
        ct.E0 = params.g_i[2].powZn(xi)
                .mul(params.g_i[3].powZn(ct.eta))
                .mul(params.g_i[4])
                .powZn(theta)
                .getImmutable();

        return ct;
    }

    /**
     * Unsigncrypt - 解签密算法（简化版）
     */
    public byte[] unsigncrypt(SystemParams params, Ciphertext ct, DecryptionKey dk) {
        // 找到匹配的属性
        Set<String> matchingAttrs = new HashSet<>(dk.attributes);

        if (matchingAttrs.isEmpty()) {
            return null;
        }

        // 使用第一个匹配的属性解密
        String matchAttr = matchingAttrs.iterator().next();
        Element D_y = dk.D_y.get(matchAttr);

        // 获取对应的加密组件
        EncComponent ec = ct.E_i.get(0);

        // 计算配对
        Element pairing1 = pairing.pairing(ec.E_i2, dk.D02).getImmutable();
        Element pairing2 = pairing.pairing(ec.E_i1, D_y).getImmutable();
        Element pairing3 = pairing.pairing(ct.E, dk.D01).getImmutable();

        // 组合得到 g_T^theta
        Element g_T_theta = pairing3.mul(pairing2).div(pairing1).getImmutable();

        // 派生密钥解密
        byte[] key = KDF(g_T_theta, ct.ct.length * 8);
        byte[] message = new byte[ct.ct.length];
        for (int i = 0; i < ct.ct.length; i++) {
            message[i] = (byte) (ct.ct[i] ^ key[i]);
        }

        return message;
    }

    /**
     * 性能测试主函数
     */
    public void runBenchmark() {
        System.out.println("========================================");
        System.out.println("属性基签密性能测试 (10-50个属性)");
        System.out.println("========================================\n");

        // 初始化系统
        System.out.println("正在初始化系统参数...");
        long setupStart = System.currentTimeMillis();
        SystemParams params = setup();
        long setupEnd = System.currentTimeMillis();
        System.out.println("系统初始化完成，耗时: " + (setupEnd - setupStart) + " ms\n");

        // 测试消息
        byte[] message = "This is a test message for ABSC scheme!".getBytes();

        // 测试不同数量的属性
        int[] attrCounts = {10, 15, 20, 25, 30, 35, 40, 45, 50};

        System.out.println("属性数量\t签名密钥生成(ms)\t解密密钥生成(ms)\t签密(ms)\t解签密(ms)\t总时间(ms)");
        System.out.println("----------------------------------------------------------------------------------------");

        for (int attrCount : attrCounts) {
            // 生成属性集
            Set<String> signingAttrs = new HashSet<>();
            Set<String> encryptionAttrs = new HashSet<>();

            for (int i = 0; i < attrCount; i++) {
                signingAttrs.add("SignAttr_" + i);
                encryptionAttrs.add("EncAttr_" + i);
            }

            // 测试签名密钥生成
            long skGenStart = System.nanoTime();
            SigningKey sk = keyGenSigning(params, signingAttrs);
            long skGenEnd = System.nanoTime();
            double skGenTime = (skGenEnd - skGenStart) / 1_000_000.0;

            // 测试解密密钥生成
            long dkGenStart = System.nanoTime();
            DecryptionKey dk = keyGenDecryption(params, encryptionAttrs);
            long dkGenEnd = System.nanoTime();
            double dkGenTime = (dkGenEnd - dkGenStart) / 1_000_000.0;

            // 测试签密
            long signcryptStart = System.nanoTime();
            Ciphertext ct = signcrypt(params, message, sk, encryptionAttrs);
            long signcryptEnd = System.nanoTime();
            double signcryptTime = (signcryptEnd - signcryptStart) / 1_000_000.0;

            // 测试解签密
            long unsigncryptStart = System.nanoTime();
            byte[] decrypted = unsigncrypt(params, ct, dk);
            long unsigncryptEnd = System.nanoTime();
            double unsigncryptTime = (unsigncryptEnd - unsigncryptStart) / 1_000_000.0;

            double totalTime = skGenTime + dkGenTime + signcryptTime + unsigncryptTime;

            // 验证正确性
            boolean correct = Arrays.equals(message, decrypted);

            System.out.printf("%d\t\t%.2f\t\t\t%.2f\t\t\t%.2f\t\t%.2f\t\t%.2f\t%s\n",
                    attrCount, skGenTime, dkGenTime, signcryptTime, unsigncryptTime,
                    totalTime, correct ? "✓" : "✗");
        }

        System.out.println("\n测试完成!");
    }

    /**
     * 主函数
     */
    public static void main(String[] args) {
        ABSCBenchmark benchmark = new ABSCBenchmark();
        benchmark.runBenchmark();
    }
}
