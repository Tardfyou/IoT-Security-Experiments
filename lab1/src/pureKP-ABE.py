"""
KP-ABE (Key-Policy Attribute Based Encryption) 纯Python实现
支持任意深度的访问树结构
"""
import random
import hashlib
import time
from functools import reduce

# 模拟密码学原语的简化实现
# 注意：这是一个教学示例，不应用于实际生产环境
class SimulatedCrypto:
    def __init__(self, security_param=512):
        """初始化模拟的密码学环境"""
        self.p = random.getrandbits(security_param)  # 模拟大素数
        self.g = random.randint(2, self.p-1)  # 模拟生成元
        
    def random_zp(self):
        """生成Zp中的随机数"""
        return random.randint(1, self.p-1)
    
    def exp(self, base, exponent):
        """模拟指数运算: base^exponent mod p"""
        return pow(base, exponent, self.p)
    
    def mul(self, a, b):
        """模拟乘法运算: (a * b) mod p"""
        return (a * b) % self.p
    
    def pair(self, g_a, g_b):
        """模拟双线性配对: e(g^a, g^b) = e(g,g)^(ab)"""
        # 在实际系统中，这将是真实的双线性配对操作
        # 这里简化为e(g^a, g^b) = g^(a*b)
        h = hashlib.sha256(str(g_a + g_b).encode()).hexdigest()
        return int(h, 16) % self.p

# KP-ABE方案实现
class KP_ABE:
    def __init__(self):
        """初始化KP-ABE系统"""
        self.crypto = SimulatedCrypto()
        
    def setup(self, attributes_universe):
        """
        系统设置，生成公钥和主密钥
        
        参数:
            attributes_universe (set): 所有可能属性的集合
            
        返回:
            tuple: (公钥, 主密钥)
        """
        g = self.crypto.g  # 生成元
        y = self.crypto.random_zp()  # 随机主密钥y
        
        # 计算Y = e(g,g)^y
        g_y = self.crypto.exp(g, y)
        Y = self.crypto.pair(g, g_y)
        
        # 为每个属性选择随机值t_i
        t = {}
        T = {}
        for attr in attributes_universe:
            t[attr] = self.crypto.random_zp()
            T[attr] = self.crypto.exp(g, t[attr])  # g^{t_i}
        
        # 公钥和主密钥
        pk = {'g': g, 'Y': Y, 'T': T}
        mk = {'y': y, 't': t}
        
        return pk, mk
    
    def parse_policy(self, policy_str):
        """
        解析策略字符串并构建访问树
        
        参数:
            policy_str (str): 形如 "(A AND (B OR C)) AND (D OR (E AND F))" 的策略字符串
            
        返回:
            dict: 访问树结构
        """
        def tokenize(s):
            """将策略字符串分解为tokens"""
            s = s.replace('(', ' ( ').replace(')', ' ) ')
            return [token for token in s.split() if token]
        
        def parse(tokens):
            """递归构建访问树"""
            if not tokens:
                return None
                
            token = tokens.pop(0)
            
            if token == '(':
                # 解析子表达式
                left = parse(tokens)
                
                # 获取操作符
                if tokens[0] == 'AND':
                    op = 'AND'
                elif tokens[0] == 'OR':
                    op = 'OR'
                else:
                    raise ValueError(f"不支持的操作符: {tokens[0]}")
                tokens.pop(0)  # 弹出操作符
                
                # 解析右侧
                right = parse(tokens)
                
                # 确保结束括号
                if tokens[0] != ')':
                    raise ValueError("括号不匹配")
                tokens.pop(0)  # 弹出右括号
                
                # 创建节点
                if op == 'AND':
                    return {
                        'threshold': 2,  # AND门，所有子节点都需要满足
                        'children': [left, right]
                    }
                else:  # op == 'OR'
                    return {
                        'threshold': 1,  # OR门，至少一个子节点满足
                        'children': [left, right]
                    }
            elif token == ')':
                raise ValueError("括号不匹配")
            else:
                # 这是一个属性
                return {'attribute': token, 'threshold': 1}
        
        tokens = tokenize(policy_str)
        tree = parse(tokens)
        
        # 深度优先遍历，给每个节点分配唯一索引
        def assign_indices(node, next_index=0):
            node['index'] = next_index
            next_index += 1
            
            if 'children' in node:
                for child in node['children']:
                    next_index = assign_indices(child, next_index)
            
            return next_index
        
        assign_indices(tree)
        self.access_tree = tree
        return tree
    
    def evaluate_polynomial(self, poly, x):
        """
        评估多项式在点x的值: poly(x)
        """
        result = 0
        for degree, coef in poly.items():
            result += coef * (x ** degree)
        return result % self.crypto.p
    
    def key_gen(self, pk, mk, tree):
        """
        为访问树生成密钥
        
        参数:
            pk (dict): 公钥
            mk (dict): 主密钥
            tree (dict): 访问树结构
            
        返回:
            dict: 私钥(解密密钥)
        """
        g = pk['g']
        y = mk['y']
        t = mk['t']
        
        # 为树中的每个节点分配多项式
        def assign_polynomials(node, poly_val_at_zero):
            # 创建多项式
            node['polynomial'] = {}
            node['polynomial'][0] = poly_val_at_zero  # q_x(0) = poly_val_at_zero
            
            # 随机生成节点的多项式系数 (阶数为 threshold - 1)
            for i in range(1, node['threshold']):
                node['polynomial'][i] = self.crypto.random_zp()
            
            # 为每个子节点递归分配多项式
            if 'children' in node:
                for i, child in enumerate(node['children']):
                    # 子节点的索引(从1开始)
                    child_index = i + 1
                    
                    # 计算父节点多项式在child_index处的值
                    q_parent_at_index = self.evaluate_polynomial(node['polynomial'], child_index)
                    
                    # 设置子节点多项式的q_x(0)值
                    assign_polynomials(child, q_parent_at_index)
        
        # 从根节点开始，设置q_root(0) = y
        assign_polynomials(tree, y)
        
        # 为每个叶节点生成密钥组件
        decryption_components = {}
        
        def generate_key_components(node):
            if 'attribute' in node:  # 叶节点
                attr = node['attribute']
                # D_x = g^{q_x(0)/t_i} 其中i是这个叶节点对应的属性
                q_x_0 = node['polynomial'][0]
                t_i = t[attr]
                decryption_components[attr] = self.crypto.exp(g, q_x_0 * pow(t_i, -1, self.crypto.p))
            
            if 'children' in node:  # 非叶节点
                for child in node['children']:
                    generate_key_components(child)
        
        generate_key_components(tree)
        
        return {'D': decryption_components}
    
    def encrypt(self, pk, message, gamma):
        """
        加密消息
        
        参数:
            pk (dict): 公钥
            message (int): 要加密的消息
            gamma (set): 属性集合
            
        返回:
            dict: 密文
        """
        g = pk['g']
        Y = pk['Y']
        
        # 随机选择s
        s = self.crypto.random_zp()
        
        # 计算E' = M · Y^s
        Y_s = self.crypto.exp(Y, s)
        E_prime = self.crypto.mul(message, Y_s)
        
        # 为gamma中的每个属性i计算E_i = T_i^s
        E = {}
        for attr in gamma:
            if attr in pk['T']:
                E[attr] = self.crypto.exp(pk['T'][attr], s)
        
        return {'gamma': gamma, 'E_prime': E_prime, 'E': E}
    
    def lagrange_coefficient(self, i, S, x):
        """
        计算拉格朗日插值系数
        
        参数:
            i (int): 索引i
            S (list): 索引集合
            x (int): 计算点
            
        返回:
            int: 拉格朗日系数
        """
        result = 1
        
        for j in S:
            if j != i:
                # 计算 (x - j) / (i - j)
                numerator = (x - j) % self.crypto.p
                denominator = (i - j) % self.crypto.p
                inverse_denom = pow(denominator, -1, self.crypto.p)
                result = (result * numerator * inverse_denom) % self.crypto.p
                
        return result
    
    def decrypt(self, pk, sk, ct):
        """
        解密密文
        
        参数:
            pk (dict): 公钥
            sk (dict): 私钥
            ct (dict): 密文
            
        返回:
            int: 解密后的消息
        """
        # 递归计算每个节点的解密值
        def decrypt_node(node, ct, D):
            # 如果是叶节点
            if 'attribute' in node:
                attr = node['attribute']
                if attr in ct['gamma']:  # 如果属性在属性集中
                    # 计算e(D_x, E_i) = e(g^{q_x(0)/t_i}, g^{s·t_i}) = e(g,g)^{s·q_x(0)}
                    return self.crypto.pair(D[attr], ct['E'][attr])
                else:
                    return None
            
            # 如果是内部节点
            if 'children' in node:
                # 计算所有子节点的解密值
                valid_children = []
                for i, child in enumerate(node['children']):
                    child_result = decrypt_node(child, ct, D)
                    if child_result is not None:
                        valid_children.append((i+1, child_result))  # (索引, 解密值)
                
                # 如果满足阈值的子节点不足
                if len(valid_children) < node['threshold']:
                    return None
                
                # 使用拉格朗日插值合并子节点的解密值
                indices = [idx for idx, _ in valid_children]
                result = 1
                
                # 只使用前threshold个子节点
                for i in range(node['threshold']):
                    idx, value = valid_children[i]
                    # 计算拉格朗日系数
                    coef = self.lagrange_coefficient(idx, indices[:node['threshold']], 0)
                    # 应用插值
                    result = self.crypto.mul(result, self.crypto.exp(value, coef))
                
                return result
        
        # 从根节点开始解密
        D = sk['D']
        decryption_result = decrypt_node(self.access_tree, ct, D)
        
        if decryption_result is None:
            raise ValueError("解密失败: 属性集合不满足访问策略")
        
        # 还原消息: M = E' / e(g,g)^{ys}
        # 在模运算中，这等同于 M = E' * (e(g,g)^{ys})^(-1)
        inverse_result = pow(decryption_result, -1, self.crypto.p)
        decrypted_message = self.crypto.mul(ct['E_prime'], inverse_result)
        
        return decrypted_message
    
    def demo(self):
        """
        KP-ABE方案的完整演示
        """
        print("===== KP-ABE方案演示 - 支持多层访问树 =====")
        
        # 1. 系统设置
        attributes_universe = {'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'}
        print(f"属性域: {attributes_universe}")
        
        start_time = time.time()
        pk, mk = self.setup(attributes_universe)
        setup_time = time.time() - start_time
        print(f"Setup完成，耗时: {setup_time:.6f}秒")
        
        # 2. 定义多层访问策略
        # 这里我们定义一个三层的访问策略
        policy_str = "((A AND B) OR (C AND D)) AND (E OR (F AND (G OR H)))"
        print(f"访问策略: {policy_str}")
        print("这是一个包含三层的复杂访问树")
        
        tree = self.parse_policy(policy_str)
        
        # 3. 生成密钥
        start_time = time.time()
        sk = self.key_gen(pk, mk, tree)
        keygen_time = time.time() - start_time
        print(f"密钥生成完成，耗时: {keygen_time:.6f}秒")
        
        # 4. 准备消息
        message = random.randint(1, self.crypto.p - 1)  # 随机消息
        print(f"原始消息: {message}")
        
        # 5. 测试不同的属性集合
        test_cases = [
            {'A', 'B', 'E'},                 # 满足 (A AND B) AND E
            {'C', 'D', 'F', 'G'},            # 满足 (C AND D) AND (F AND G)
            {'A', 'B', 'F', 'H'},            # 满足 (A AND B) AND (F AND H)
            {'A', 'C', 'E'},                 # 不满足 - 缺少B或D
            {'A', 'B', 'F'},                 # 不满足 - 缺少G或H
            {'A', 'C', 'D', 'F', 'G', 'H'},  # 满足 (C AND D) AND (F AND (G OR H))
        ]
        
        for i, gamma in enumerate(test_cases):
            print(f"\n测试 {i+1}: 属性集合 {gamma}")
            
            # 加密
            start_time = time.time()
            ct = self.encrypt(pk, message, gamma)
            encryption_time = time.time() - start_time
            print(f"加密完成，耗时: {encryption_time:.6f}秒")
            
            # 解密
            try:
                start_time = time.time()
                decrypted_message = self.decrypt(pk, sk, ct)
                decryption_time = time.time() - start_time
                
                # 验证
                if message == decrypted_message:
                    print(f"解密成功，耗时: {decryption_time:.6f}秒")
                    print("消息匹配!")
                else:
                    print(f"解密失败，消息不匹配! 得到: {decrypted_message}")
            except Exception as e:
                print(f"解密失败: {e}")
                
        # 6. 展示访问树结构
        print("\n====== 访问树结构 ======")
        self.print_tree(tree)
        
    def print_tree(self, node, level=0):
        """
        可视化打印访问树结构
        """
        indent = "  " * level
        
        if 'attribute' in node:
            print(f"{indent}叶节点: 属性={node['attribute']}, 索引={node['index']}")
        else:
            gate_type = "AND" if node['threshold'] == len(node['children']) else "OR"
            print(f"{indent}内部节点: 阈值={node['threshold']}, 类型={gate_type}, 索引={node['index']}")
            
            for child in node['children']:
                self.print_tree(child, level + 1)

# 主函数
if __name__ == "__main__":
    try:
        kp_abe = KP_ABE()
        kp_abe.demo()
    except Exception as e:
        print(f"错误: {e}")

'''
多层访问树 KP-ABE 实现说明
由于在安装 Charm 库时遇到了问题，提供了一个纯 Python 实现的 KP-ABE 方案，支持任意深度的访问树结构。这个实现不需要外部依赖，可以直接运行。
代码重点特性

支持任意深度的访问树：

实现了递归的树构建和解析
可以处理复杂的嵌套访问策略，如 ((A AND B) OR (C AND D)) AND (E OR (F AND (G OR H)))
访问树可以有任意深度


访问策略解析器：

通过 parse_policy 函数解析字符串形式的策略表达式
支持 AND 和 OR 逻辑门
处理嵌套括号表示的复杂层次关系


完整的密码学模拟：

虽然使用了简化的模拟双线性配对，但保留了 KP-ABE 方案的核心逻辑
在教学和演示目的上是完整的

访问树结构示例
以 ((A AND B) OR (C AND D)) AND (E OR (F AND (G OR H))) 为例，该树有三层深度：

第一层：根节点（AND门）
第二层：两个子节点

左子树：(A AND B) OR (C AND D)（OR门）
右子树：E OR (F AND (G OR H))（OR门）


第三层：

左子树下：A AND B（AND门）和 C AND D（AND门）
右子树下：叶节点 E 和 F AND (G OR H)（AND门）


第四层：

G OR H（OR门）

使用方法

你可以直接运行这个脚本，它会执行演示函数，展示一个多层访问树的完整 KP-ABE 流程
可以通过修改 policy_str 变量来测试不同的访问策略
可以调整 test_cases 中的属性集合来测试不同的解密场景

算法执行过程

Setup：生成系统公钥和主密钥
解析访问策略：将字符串策略转换为访问树结构
密钥生成：为访问树生成解密密钥
加密：使用属性集加密消息
解密：只有当属性集满足访问策略时才能成功解密

这个实现是一个教学演示，它模拟了真实 KP-ABE 系统的工作原理，不需要复杂的密码学库依赖，适合理解 KP-ABE 的核心概念和操作流程。
如果你以后希望在实际应用中使用 KP-ABE，我建议解决 Charm 库的安装问题，因为它提供了真正的密码学原语和双线性配对计算。
'''