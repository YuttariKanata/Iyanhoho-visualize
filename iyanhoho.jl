using DataStructures
using ProgressMeter

"""
配列 `s` の中にある `from_pattern` を、1箇所だけ `to_pattern` に置換した全パターンの集合
"""
function replace_one_pattern(s::Vector{Int}, from_pattern::Vector{Int}, to_pattern::Vector{Int})
    states = Set{Vector{Int}}()
    len_s = length(s)
    len_from = length(from_pattern)
    
    for i in 1:(len_s - len_from + 1)
        if @views s[i:(i + len_from - 1)] == from_pattern
            new_s = vcat(s[1:(i - 1)], to_pattern, s[(i + len_from):end])
            push!(states, new_s)
        end
    end
    return states
end

"""
現在の状態から、ルールに基づいて次に行ける状態をすべて生成する
"""
function get_next_vector_states(s::Vector{Int}; allow_same_char::Bool=true)
    next_states = Set{Vector{Int}}()
    len = length(s)
    if len < 2 return next_states end
    
    # 1. 正方向ルール: xy -> yxx
    for i in 1:(len - 1)
        x = s[i]
        y = s[i+1]
        
        if !allow_same_char && x == y
            continue
        end
        
        union!(next_states, replace_one_pattern(s, [x, y], [y, x, x]))
    end
    
    # 2. 逆方向ルール: yxx -> xy
    for i in 1:(len - 2)
        y_val = s[i]
        x1_val = s[i+1]
        x2_val = s[i+2]
        
        if x1_val == x2_val  # 後ろ2文字が同じ (YXX構造)
            if !allow_same_char && y_val == x1_val
                continue
            end
            union!(next_states, replace_one_pattern(s, [y_val, x1_val, x2_val], [x1_val, y_val]))
        end
    end
    
    return next_states
end

"""
文字列を Vector{Int} に変換して到達可能性を【双方向BFS】で検証する関数
"""
function bidirectional_bfs_prove(start_str::String, target_str::String; allow_same_char::Bool=true, max_depth::Int=20, max_length::Int=15)
    all_chars = unique(start_str * target_str)
    char_to_id = Dict(c => i for (i, c) in enumerate(all_chars))
    id_to_char = Dict(i => c for (i, c) in enumerate(all_chars))
    
    start_vec = [char_to_id[c] for c in start_str]
    target_vec = [char_to_id[c] for c in target_str]
    
    if start_vec == target_vec
        println("🎉 初期状態と目標状態が同じです！")
        return true
    end
    
    forward_visited = Dict{Vector{Int}, Vector{Int}}(start_vec => start_vec)
    backward_visited = Dict{Vector{Int}, Vector{Int}}(target_vec => target_vec)
    
    forward_layer = Set{Vector{Int}}([start_vec])
    backward_layer = Set{Vector{Int}}([target_vec])
    
    vec_to_str(v) = join([id_to_char[i] for i in v])
    
    println("==================================================")
    println("🔮 双方向代数パズル検証 (挟み撃ち最速版)")
    println("初期状態: ", start_str, " ↔ 目標状態: ", target_str)
    println("ルール設定: ", allow_same_char ? "【A】xx=xxx を許可" : "【B】xx=xxx 禁止")
    println("最大合計深さ: ", max_depth, " (最大文字数制限: ", max_length, ")")
    println("==================================================")
    
    found = false
    collision_node = Int[]
    
    for step in 1:max_depth
        if isempty(forward_layer) || isempty(backward_layer)
            break
        end
        
        if length(forward_layer) <= length(backward_layer)
            next_layer = Set{Vector{Int}}()
            layer_elements = collect(forward_layer)
            
            @showprogress "Forward Layer Expansion in Progress: " for curr in layer_elements
                next_nodes = get_next_vector_states(curr, allow_same_char=allow_same_char)
                for nxt in next_nodes
                    if length(nxt) > max_length continue end
                    
                    if haskey(backward_visited, nxt)
                        forward_visited[nxt] = curr
                        collision_node = nxt
                        found = true
                        break
                    end
                    
                    if !haskey(forward_visited, nxt)
                        forward_visited[nxt] = curr
                        push!(next_layer, nxt)
                    end
                end
                if found break end
            end
            forward_layer = next_layer
        else
            next_layer = Set{Vector{Int}}()
            layer_elements = collect(backward_layer)
            
            @showprogress "Backward Layer Expansion in Progress: " for curr in layer_elements
                next_nodes = get_next_vector_states(curr, allow_same_char=allow_same_char)
                for nxt in next_nodes
                    if length(nxt) > max_length continue end
                    
                    if haskey(forward_visited, nxt)
                        backward_visited[nxt] = curr
                        collision_node = nxt
                        found = true
                        break
                    end
                    
                    if !haskey(backward_visited, nxt)
                        backward_visited[nxt] = curr
                        push!(next_layer, nxt)
                    end
                end
                if found break end
            end
            backward_layer = next_layer
        end
        
        if found break end
    end
    
    if found
        # --- 経路の復元 ---
        f_path = [collision_node]
        curr = collision_node
        while curr != start_vec
            curr = forward_visited[curr]
            push!(f_path, curr)
        end
        reverse!(f_path)
        
        b_path = Vector{Int}[]
        curr = collision_node
        while curr != target_vec
            curr = backward_visited[curr]
            push!(b_path, curr)
        end
        
        full_path = vcat(f_path, b_path)
        
        println("\n🎉 証明成功！ $start_str = $target_str が成り立ちます。")
        println("最短手順: ", length(full_path) - 1, " 手 (衝突ノード: ", vec_to_str(collision_node), ")")
        println("\n【変形経路】")
        println(join([vec_to_str(v) for v in full_path], "\n"))
    else
        total_explored = length(forward_visited) + length(backward_visited)
        println("\n❌ 合計深さ ", max_depth, "（文字数制限: ", max_length, "）の範囲では挟み撃ちできませんでした。")
        println("探索した総ユニーク状態数: ", total_explored)
    end
    println("="^50 * "\n")
    return found
end

# 実行
bidirectional_bfs_prove("ABCD", "DCBA", allow_same_char=true, max_depth=30, max_length=16)