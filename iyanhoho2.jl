using DataStructures
using ProgressMeter

const MAX_LEN = 31
const Word = NTuple{MAX_LEN + 1, UInt8}

"""
Vector{Int} を 固定長スタック構造 Word (NTuple) にエンコード
"""
function encode_word(vec::Vector{Int})::Word
    L = length(vec)
    @assert L <= MAX_LEN "文字列が MAX_LEN ($MAX_LEN) を超えています"
    return ntuple(i -> i == 1 ? UInt8(L) : (i-1 <= L ? UInt8(vec[i-1]) : 0x00), Val(MAX_LEN + 1))
end

"""
Word (NTuple) を Vector{Int} にデコード (表示用：実際の長さ L 分だけ切り出す)
"""
function decode_word(w::Word)::Vector{Int}
    L = Int(w[1])
    # w[2] から w[L+1] までが実際の文字データ
    return [Int(w[i]) for i in 2:(L+1)]
end

using StaticArrays

"""
インプレースに変形状態を生成する (完全に安全なpushベース・ゼロアロケーション版)
"""
function get_next_states!(next_states::Set{Word}, w::Word, allow_same_char::Bool)
    L = Int(w[1])
    if L < 2 return end
    
    # スレッドローカル（または関数ローカル）な書き換え用作業領域。
    # インデックス計算を排除し、安全に文字を push! するためのバッファ。
    # MVector なのでヒープアロケーションはゼロ。
    buf = MVector{MAX_LEN, UInt8}(undef)
    
    # 1. 正方向ルール: xy -> yxx (長さが L+1 になる)
    if L + 1 <= MAX_LEN
        for i in 1:(L - 1)
            # w[2] から w[L+1] が実際の文字データ
            # 隣り合うペアは w[i+1] と w[i+2]
            x = w[i+1]
            y = w[i+2]
            if !allow_same_char && x == y
                continue
            end
            
            # バッファのクリア（インデックス管理用ポインタ）
            idx = 1
            
            # 挿入位置の手前までコピー
            for j in 1:(i-1)
                buf[idx] = w[j+1]
                idx += 1
            end
            # xy -> yxx を配置
            buf[idx]   = y
            buf[idx+1] = x
            buf[idx+2] = x
            idx += 3
            # 残りの文字をコピー
            for j in (i+2):L
                buf[idx] = w[j+1]
                idx += 1
            end
            
            # 固定長 Word (NTuple) へビルド
            # 1番目に長さ、2番目以降にデータ、残りは 0x00
            nxt = ntuple(Val(MAX_LEN + 1)) do k
                if k == 1
                    return UInt8(L + 1)
                elseif k-1 <= L + 1
                    return buf[k-1]
                else
                    return 0x00
                end
            end
            push!(next_states, nxt)
        end
    end
    
    # 2. 逆方向ルール: yxx -> xy (長さが L-1 になる)
    for i in 1:(L - 2)
        # 3文字の並びは w[i+1], w[i+2], w[i+3]
        y  = w[i+1]
        x1 = w[i+2]
        x2 = w[i+3]
        
        if x1 == x2
            if !allow_same_char && y == x1
                continue
            end
            
            idx = 1
            # 置換位置の手前までコピー
            for j in 1:(i-1)
                buf[idx] = w[j+1]
                idx += 1
            end
            # yxx -> xy を配置
            buf[idx]   = x1
            buf[idx+1] = y
            idx += 2
            # 残りの文字をコピー
            for j in (i+3):L
                buf[idx] = w[j+1]
                idx += 1
            end
            
            nxt = ntuple(Val(MAX_LEN + 1)) do k
                if k == 1
                    return UInt8(L - 1)
                elseif k-1 <= L - 1
                    return buf[k-1]
                else
                    return 0x00
                end
            end
            push!(next_states, nxt)
        end
    end
end

"""
超高速版 双方向BFS
"""
function bidirectional_bfs_prove_fast(start_str::String, target_str::String; allow_same_char::Bool=true, max_depth::Int=40, max_length::Int=30)
    all_chars = unique(start_str * target_str)
    char_to_id = Dict(c => i for (i, c) in enumerate(all_chars))
    id_to_char = Dict(i => c for (i, c) in enumerate(all_chars))
    
    start_vec = [char_to_id[c] for c in start_str]
    target_vec = [char_to_id[c] for c in target_str]
    
    start_word = encode_word(start_vec)
    target_word = encode_word(target_vec)
    
    if start_word == target_word
        println("🎉 初期状態と目標状態が同じです！")
        return true
    end
    
    # 親ノード保持用 Dict (ハッシュ効率最高)
    forward_visited = Dict{Word, Word}(start_word => start_word)
    backward_visited = Dict{Word, Word}(target_word => target_word)
    
    forward_layer = Set{Word}([start_word])
    backward_layer = Set{Word}([target_word])
    
    # 次のレイヤー展開用の一時バッファ (使い回すことでアロケーションを排除)
    next_layer_buf = Set{Word}()
    # 各ノードからの遷移先を一時的に格納するバッファ
    local_transitions = Set{Word}()
    
    # 修正：タプルの1番目の要素（長さL）を厳密に読み込み、余白の0x00を完全に無視する
    word_to_str(w) = join([id_to_char[Int(w[i])] for i in 2:(Int(w[1]) + 1)])
    
    println("==================================================")
    println("🚀 双方向代数パズル検証 (ゼロアロケーション版)")
    println("初期状態: ", start_str, " ↔ 目標状態: ", target_str)
    println("最大合計深さ: ", max_depth, " (最大文字数制限: ", max_length, ")")
    println("==================================================")
    
    found = false
    collision_node = start_word
    
    for step in 1:max_depth
        if isempty(forward_layer) || isempty(backward_layer)
            break
        end
        
        empty!(next_layer_buf)
        
        if length(forward_layer) <= length(backward_layer)
            # Forward 展開
            @showprogress "Forward Layer $step: " for curr in forward_layer
                empty!(local_transitions)
                get_next_states!(local_transitions, curr, allow_same_char)
                
                for nxt in local_transitions
                    if Int(nxt[1]) > max_length continue end
                    
                    if haskey(backward_visited, nxt)
                        forward_visited[nxt] = curr
                        collision_node = nxt
                        found = true
                        break
                    end
                    
                    if !haskey(forward_visited, nxt)
                        forward_visited[nxt] = curr
                        push!(next_layer_buf, nxt)
                    end
                end
                if found break end
            end
            # レイヤーの入れ替え (バッファを再利用)
            forward_layer, next_layer_buf = next_layer_buf, forward_layer
        else
            # Backward 展開
            @showprogress "Backward Layer $step: " for curr in backward_layer
                empty!(local_transitions)
                get_next_states!(local_transitions, curr, allow_same_char)
                
                for nxt in local_transitions
                    if Int(nxt[1]) > max_length continue end
                    
                    if haskey(forward_visited, nxt)
                        backward_visited[nxt] = curr
                        collision_node = nxt
                        found = true
                        break
                    end
                    
                    if !haskey(backward_visited, nxt)
                        backward_visited[nxt] = curr
                        push!(next_layer_buf, nxt)
                    end
                end
                if found break end
            end
            # レイヤーの入れ替え
            backward_layer, next_layer_buf = next_layer_buf, backward_layer
        end
        
        if found break end
    end
    
    if found
        # 1. Forward 経路の復元: [start_word -> ... -> collision_node]
        f_path = Word[]
        curr = collision_node
        push!(f_path, curr)
        while curr != start_word
            curr = forward_visited[curr]
            push!(f_path, curr)
        end
        reverse!(f_path) # 始点から衝突ノードへの順にする
        
        # 2. : [target_word -> ... -> collision_node] を遡る
        # つまり、collision_node から target_word への順に回収する
        b_path = Word[]
        curr = collision_node
        while curr != target_word
            curr = backward_visited[curr]
            push!(b_path, curr)
        end
        # ※ collision_node は f_path の末尾にあるので、b_path からは除外して結合する
        
        full_path = vcat(f_path, b_path)
        
        println("\n🎉 証明成功！ $start_str = $target_str")
        println("最短手順: ", length(full_path) - 1, " 手")
        println("\n【変形経路】")
        for w in full_path
            # 万が一、長さが0の不正ノードが紛れ込んでも例外を吐かせないガード
            if w[1] == 0
                println("(empty/invalid)")
                continue
            end
            println(word_to_str(w))
        end
    else
        total_explored = length(forward_visited) + length(backward_visited)
        println("\n❌ 解が見つかりませんでした。")
        println("探索した総ユニーク状態数: ", total_explored)
    end
    return found
end

# 実行検証
bidirectional_bfs_prove_fast("ハロウイーン", "ウーロンハイ", allow_same_char=true, max_depth=30, max_length=16)