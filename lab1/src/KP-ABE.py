from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT, pair
from charm.core.engine.util import objectToBytes
import random
import time

class KP_ABE:
    def __init__(self):
        # 初始化配对群
        self.group = PairingGroup('SS512')  # 使用 SS512 曲线
        
    def setup(self, attributes_universe):
        """
        系统设置，生成公钥和主密钥
        
        输入：
        - attributes_universe: 所有可能属性的集合
        
        输出:
        - PK: 公开参数
        - MK: 主密钥
        """
        g = self.group.random(G1)  # 生成 G1 群的生成元
        y = self.group.random(ZR)  # 随机选择 y
        Y = pair(g, g) ** y  # e(g,g)^y
        
        # 为每个属性选择随机值 t_i
        t = {}
        T = {}
        for i in attributes_universe:
            t[i] = self.group.random(ZR)
            T[i] = g ** t[i]  # g^{t_i}
        
        pk = {'g': g, 'Y': Y, 'T': T}
        mk = {'y': y, 't': t}
        
        return pk, mk
    
    def key_gen(self, pk, mk, tree):
        """
        密钥生成算法
        
        输入:
        - pk: 公开参数
        - mk: 主密钥
        - tree: 访问树
        
        输出:
        - sk: 私钥（解密密钥）
        """
        # 提取主密钥参数
        y = mk['y']
        t = mk['t']
        g = pk['g']
        
        # 为树节点分配多项式的递归函数
        def assign_polynomials(node, poly_val_at_zero):
            # 为当前节点创建多项式
            node['polynomial'] = {}
            node['polynomial'][0] = poly_val_at_zero  # q_x(0) 的值
            
            # 随机选择 d_x = k_x - 1 个点来定义 k_x - 1 阶多项式
            degree = node['threshold'] - 1
            for i in range(1, degree + 1):
                node['polynomial'][i] = self.group.random(ZR)
            
            # 为每个子节点计算多项式值并递归
            if 'children' in node:
                for i, child in enumerate(node['children']):
                    child_index = i + 1  # 子节点索引从1开始
                    
                    # 在索引 child_index 处评估当前节点的多项式
                    value_at_child_index = self.evaluate_polynomial(node['polynomial'], child_index)
                    
                    # 递归到子节点
                    assign_polynomials(child, value_at_child_index)
        
        # 为根节点的多项式赋值 q_r(0) = y，然后递归到其他节点
        assign_polynomials(tree, y)
        
        # 生成解密密钥的递归函数
        def generate_decryption_components(node, D):
            if 'attribute' in node:  # 叶节点
                attr = node['attribute']
                D[attr] = g ** (node['polynomial'][0] / t[attr])
            elif 'children' in node:  # 非叶节点
                for child in node['children']:
                    generate_decryption_components(child, D)
        
        # 生成所有解密组件
        D = {}
        generate_decryption_components(tree, D)
        
        return {'D': D}
    
    def encrypt(self, pk, message, gamma):
        """
        加密算法
        
        输入:
        - pk: 公开参数
        - message: 要加密的消息 (GT 中的元素)
        - gamma: 属性集合
        
        输出:
        - ct: 密文
        """
        s = self.group.random(ZR)  # 随机数 s
        g = pk['g']
        Y = pk['Y']
        
        E_prime = message * (Y ** s)  # M * Y^s
        
        # 对每个属性计算 E_i
        E = {}
        for i in gamma:
            if i in pk['T']:
                E[i] = pk['T'][i] ** s  # T_i^s
        
        return {'gamma': gamma, 'E_prime': E_prime, 'E': E}
    
    def decrypt(self, pk, sk, ct):
        """
        解密算法
        
        输入:
        - pk: 公开参数
        - sk: 私钥
        - ct: 密文
        
        输出:
        - message: 解密后的消息
        """
        def decrypt_node(node, ct, D):
            """递归函数，用于计算每个节点的解密值"""
            
            # 如果是叶节点
            if 'attribute' in node:
                attr = node['attribute']
                if attr in ct['gamma']:  # 如果属性在密文的属性集中
                    return pair(D[attr], ct['E'][attr])  # e(D_x, E_i)
                else:
                    return None
            
            # 如果是内部节点
            if 'children' in node:
                # 递归解密所有子节点
                values = []
                indices = []
                
                for i, child in enumerate(node['children']):
                    child_value = decrypt_node(child, ct, D)
                    if child_value is not None:
                        values.append(child_value)
                        indices.append(i + 1)  # 子节点索引从1开始
                    
                    # 如果已收集足够的子节点满足阈值，则停止
                    if len(values) >= node['threshold']:
                        break
                
                # 如果收集到的子节点数不足以满足阈值
                if len(values) < node['threshold']:
                    return None
                
                # 计算拉格朗日插值系数并应用
                result = self.group.init(GT, 1)
                for i in range(node['threshold']):
                    coef = self.lagrange_coefficient(indices[i], indices[:node['threshold']], 0)
                    result *= values[i] ** coef
                
                return result
        
        # 从根节点开始解密
        D = sk['D']
        root_value = decrypt_node(self.access_tree, ct, D)
        
        if root_value is None:
            raise ValueError("无法解密：属性集合不满足访问结构")
        
        # 恢复消息: M = E' / e(g,g)^{ys}
        return ct['E_prime'] / root_value
    
    def evaluate_polynomial(self, polynomial, x):
        """
        评估多项式在点 x 的值
        
        输入:
        - polynomial: 表示为字典的多项式，键是次数，值是系数
        - x: 要评估的点
        
        输出:
        - 多项式在点 x 的值
        """
        result = self.group.init(ZR, 0)
        for degree, coef in polynomial.items():
            result += coef * (x ** degree)
        return result
    
    def lagrange_coefficient(self, i, S, x):
        """
        计算拉格朗日插值系数
        
        输入:
        - i: 当前点的索引
        - S: 所有点的索引集合
        - x: 要插值的点
        
        输出:
        - 拉格朗日系数
        """
        numerator = self.group.init(ZR, 1)
        denominator = self.group.init(ZR, 1)
        
        for j in S:
            if j != i:
                numerator *= (x - j)
                denominator *= (i - j)
        
        return numerator / denominator
    
    def create_access_tree(self, policy):
        """
        创建访问树的辅助函数
        
        输入:
        - policy: 策略描述
        
        输出:
        - 访问树结构
        """
        # 支持三层结构的访问树
        if policy == "(A AND B AND (C OR D)) OR (E AND F)":
            tree = {
                'threshold': 1,  # 根节点: OR门
                'children': [
                    {
                        'threshold': 3,  # 第二层第一个节点: AND门，需要3个子节点都满足
                        'children': [
                            {'attribute': 'A', 'threshold': 1},  # 第三层叶节点
                            {'attribute': 'B', 'threshold': 1},  # 第三层叶节点
                            {
                                'threshold': 1,  # 第三层内部节点: OR门
                                'children': [
                                    {'attribute': 'C', 'threshold': 1},  # 第四层叶节点
                                    {'attribute': 'D', 'threshold': 1}   # 第四层叶节点
                                ]
                            }
                        ]
                    },
                    {
                        'threshold': 2,  # 第二层第二个节点: AND门
                        'children': [
                            {'attribute': 'E', 'threshold': 1},  # 第三层叶节点
                            {'attribute': 'F', 'threshold': 1}   # 第三层叶节点
                        ]
                    }
                ]
            }
        elif policy == "((A OR B) AND (C OR D)) OR (E AND F AND G)":
            tree = {
                'threshold': 1,  # 根节点: OR门
                'children': [
                    {
                        'threshold': 2,  # 第二层第一个节点: AND门
                        'children': [
                            {
                                'threshold': 1,  # 第三层内部节点: OR门
                                'children': [
                                    {'attribute': 'A', 'threshold': 1},  # 第四层叶节点
                                    {'attribute': 'B', 'threshold': 1}   # 第四层叶节点
                                ]
                            },
                            {
                                'threshold': 1,  # 第三层内部节点: OR门
                                'children': [
                                    {'attribute': 'C', 'threshold': 1},  # 第四层叶节点
                                    {'attribute': 'D', 'threshold': 1}   # 第四层叶节点
                                ]
                            }
                        ]
                    },
                    {
                        'threshold': 3,  # 第二层第二个节点: AND门
                        'children': [
                            {'attribute': 'E', 'threshold': 1},  # 第三层叶节点
                            {'attribute': 'F', 'threshold': 1},  # 第三层叶节点
                            {'attribute': 'G', 'threshold': 1}   # 第三层叶节点
                        ]
                    }
                ]
            }
        elif policy == "(A AND B) OR (C AND D) OR E":
            tree = {
                'threshold': 1,  # 根节点: OR门
                'children': [
                    {
                        'threshold': 2,  # 第二层第一个节点: AND门
                        'children': [
                            {'attribute': 'A', 'threshold': 1},  # 第三层叶节点
                            {'attribute': 'B', 'threshold': 1}   # 第三层叶节点
                        ]
                    },
                    {
                        'threshold': 2,  # 第二层第二个节点: AND门
                        'children': [
                            {'attribute': 'C', 'threshold': 1},  # 第三层叶节点
                            {'attribute': 'D', 'threshold': 1}   # 第三层叶节点
                        ]
                    },
                    {'attribute': 'E', 'threshold': 1}  # 第二层叶节点
                ]
            }
        else:
            raise ValueError("不支持的策略格式")
            
        self.access_tree = tree
        return tree
    
    def print_access_tree(self, node=None, level=0):
        """
        打印访问树结构，方便可视化
        
        输入:
        - node: 当前节点
        - level: 当前层级
        """
        if node is None:
            node = self.access_tree
            print("======= 访问树结构 =======")
        
        indent = "  " * level
        
        if 'attribute' in node:
            print(f"{indent}叶节点: 属性 {node['attribute']}")
        else:
            gate_type = "OR" if node['threshold'] == 1 else "AND" if node['threshold'] == len(node['children']) else f"阈值({node['threshold']})"
            print(f"{indent}内部节点: {gate_type} 门, 阈值 = {node['threshold']}")
            
            for i, child in enumerate(node['children']):
                print(f"{indent}  子节点 {i+1}:")
                self.print_access_tree(child, level + 2)
    
    def demo(self):
        """
        演示KP-ABE方案的完整工作流程，使用三层访问树
        """
        print("======= KP-ABE方案演示 (三层访问树) =======")
        
        # 1. 系统设置
        attributes_universe = {'A', 'B', 'C', 'D', 'E', 'F', 'G'}
        print(f"属性域: {attributes_universe}")
        
        start_time = time.time()
        pk, mk = self.setup(attributes_universe)
        setup_time = time.time() - start_time
        print(f"Setup完成，耗时：{setup_time:.6f}秒")
        
        # 2. 创建访问树并生成密钥
        policy = "(A AND B AND (C OR D)) OR (E AND F)"
        print(f"访问策略: {policy}")
        
        tree = self.create_access_tree(policy)
        self.print_access_tree()
        
        start_time = time.time()
        sk = self.key_gen(pk, mk, tree)
        keygen_time = time.time() - start_time
        print(f"密钥生成完成，耗时：{keygen_time:.6f}秒")
        
        # 3. 加密消息
        message = self.group.random(GT)  # 随机消息用于演示
        print("生成随机消息")
        
        # 测试不同的属性集
        test_cases = [
            {'A', 'B', 'C'},           # 满足(A AND B AND (C OR D))部分
            {'A', 'B', 'D'},           # 满足(A AND B AND (C OR D))部分
            {'E', 'F'},                # 满足(E AND F)部分
            {'A', 'B'},                # 不满足完整策略
            {'A', 'C', 'D'},           # 不满足完整策略
            {'A', 'B', 'C', 'E', 'F'}  # 同时满足两个分支
        ]
        
        for gamma in test_cases:
            print(f"\n测试属性集: {gamma}")
            
            start_time = time.time()
            ct = self.encrypt(pk, message, gamma)
            encryption_time = time.time() - start_time
            print(f"加密完成，耗时：{encryption_time:.6f}秒")
            
            # 4. 解密尝试
            try:
                start_time = time.time()
                decrypted_message = self.decrypt(pk, sk, ct)
                decryption_time = time.time() - start_time
                
                # 验证解密是否正确
                if message == decrypted_message:
                    print(f"解密成功，耗时：{decryption_time:.6f}秒")
                    print("原始消息和解密消息匹配!")
                else:
                    print("解密失败，消息不匹配!")
            except Exception as e:
                print(f"解密失败: {e}")
        
        # 测试另一个复杂的访问策略
        print("\n\n======= 测试另一个三层访问树 =======")
        policy = "((A OR B) AND (C OR D)) OR (E AND F AND G)"
        print(f"访问策略: {policy}")
        
        tree = self.create_access_tree(policy)
        self.print_access_tree()
        
        start_time = time.time()
        sk = self.key_gen(pk, mk, tree)
        keygen_time = time.time() - start_time
        print(f"密钥生成完成，耗时：{keygen_time:.6f}秒")
        
        # 测试不同的属性集
        test_cases = [
            {'A', 'C'},                # 满足((A OR B) AND (C OR D))部分
            {'B', 'D'},                # 满足((A OR B) AND (C OR D))部分
            {'E', 'F', 'G'},           # 满足(E AND F AND G)部分
            {'A', 'B'},                # 不满足完整策略
            {'C', 'D'},                # 不满足完整策略
            {'E', 'F'}                 # 不满足完整策略
        ]
        
        for gamma in test_cases:
            print(f"\n测试属性集: {gamma}")
            
            start_time = time.time()
            ct = self.encrypt(pk, message, gamma)
            encryption_time = time.time() - start_time
            print(f"加密完成，耗时：{encryption_time:.6f}秒")
            
            # 解密尝试
            try:
                start_time = time.time()
                decrypted_message = self.decrypt(pk, sk, ct)
                decryption_time = time.time() - start_time
                
                # 验证解密是否正确
                if message == decrypted_message:
                    print(f"解密成功，耗时：{decryption_time:.6f}秒")
                    print("原始消息和解密消息匹配!")
                else:
                    print("解密失败，消息不匹配!")
            except Exception as e:
                print(f"解密失败: {e}")

# 主函数：使用KP-ABE
if __name__ == "__main__":
    try:
        kp_abe = KP_ABE()
        kp_abe.demo()
    except Exception as e:
        print(f"错误: {e}")