import Init.Data.BitVec

namespace KeccakEngine.Unrolled

def round_0 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x1#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_1 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8082#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_2 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x800000000000808a#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_3 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8000000080008000#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_4 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x808b#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_5 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x80000001#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_6 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8000000080008081#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_7 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8000000000008009#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_8 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8a#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_9 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x88#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_10 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x80008009#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_11 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8000000a#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_12 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8000808b#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_13 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x800000000000008b#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_14 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8000000000008089#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_15 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8000000000008003#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_16 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8000000000008002#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_17 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8000000000000080#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_18 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x800a#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_19 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x800000008000000a#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_20 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8000000080008081#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_21 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8000000000008080#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_22 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x80000001#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
def round_23 (state : Fin 25 → BitVec 64) : Fin 25 → BitVec 64 := 
  let v0 := state 0
  let v1 := state 1
  let v2 := state 2
  let v3 := state 3
  let v4 := state 4
  let v5 := state 5
  let v6 := state 6
  let v7 := state 7
  let v8 := state 8
  let v9 := state 9
  let v10 := state 10
  let v11 := state 11
  let v12 := state 12
  let v13 := state 13
  let v14 := state 14
  let v15 := state 15
  let v16 := state 16
  let v17 := state 17
  let v18 := state 18
  let v19 := state 19
  let v20 := state 20
  let v21 := state 21
  let v22 := state 22
  let v23 := state 23
  let v24 := state 24
  let v25 := v0 ^^^ v5
  let v26 := v25 ^^^ v10
  let v27 := v26 ^^^ v15
  let v28 := v27 ^^^ v20
  let v29 := v1 ^^^ v6
  let v30 := v29 ^^^ v11
  let v31 := v30 ^^^ v16
  let v32 := v31 ^^^ v21
  let v33 := v2 ^^^ v7
  let v34 := v33 ^^^ v12
  let v35 := v34 ^^^ v17
  let v36 := v35 ^^^ v22
  let v37 := v3 ^^^ v8
  let v38 := v37 ^^^ v13
  let v39 := v38 ^^^ v18
  let v40 := v39 ^^^ v23
  let v41 := v4 ^^^ v9
  let v42 := v41 ^^^ v14
  let v43 := v42 ^^^ v19
  let v44 := v43 ^^^ v24
  let v45 := v32.rotateLeft 1
  let v46 := v44 ^^^ v45
  let v47 := v36.rotateLeft 1
  let v48 := v28 ^^^ v47
  let v49 := v40.rotateLeft 1
  let v50 := v32 ^^^ v49
  let v51 := v44.rotateLeft 1
  let v52 := v36 ^^^ v51
  let v53 := v28.rotateLeft 1
  let v54 := v40 ^^^ v53
  let v55 := v0 ^^^ v46
  let v56 := v5 ^^^ v46
  let v57 := v10 ^^^ v46
  let v58 := v15 ^^^ v46
  let v59 := v20 ^^^ v46
  let v60 := v1 ^^^ v48
  let v61 := v6 ^^^ v48
  let v62 := v11 ^^^ v48
  let v63 := v16 ^^^ v48
  let v64 := v21 ^^^ v48
  let v65 := v2 ^^^ v50
  let v66 := v7 ^^^ v50
  let v67 := v12 ^^^ v50
  let v68 := v17 ^^^ v50
  let v69 := v22 ^^^ v50
  let v70 := v3 ^^^ v52
  let v71 := v8 ^^^ v52
  let v72 := v13 ^^^ v52
  let v73 := v18 ^^^ v52
  let v74 := v23 ^^^ v52
  let v75 := v4 ^^^ v54
  let v76 := v9 ^^^ v54
  let v77 := v14 ^^^ v54
  let v78 := v19 ^^^ v54
  let v79 := v24 ^^^ v54
  let v80 := v56.rotateLeft 36
  let v81 := v57.rotateLeft 3
  let v82 := v58.rotateLeft 41
  let v83 := v59.rotateLeft 18
  let v84 := v60.rotateLeft 1
  let v85 := v61.rotateLeft 44
  let v86 := v62.rotateLeft 10
  let v87 := v63.rotateLeft 45
  let v88 := v64.rotateLeft 2
  let v89 := v65.rotateLeft 62
  let v90 := v66.rotateLeft 6
  let v91 := v67.rotateLeft 43
  let v92 := v68.rotateLeft 15
  let v93 := v69.rotateLeft 61
  let v94 := v70.rotateLeft 28
  let v95 := v71.rotateLeft 55
  let v96 := v72.rotateLeft 25
  let v97 := v73.rotateLeft 21
  let v98 := v74.rotateLeft 56
  let v99 := v75.rotateLeft 27
  let v100 := v76.rotateLeft 20
  let v101 := v77.rotateLeft 39
  let v102 := v78.rotateLeft 8
  let v103 := v79.rotateLeft 14
  let v104 := ~~~v85
  let v105 := v104 &&& v91
  let v106 := v55 ^^^ v105
  let v107 := ~~~v100
  let v108 := v107 &&& v81
  let v109 := v94 ^^^ v108
  let v110 := ~~~v90
  let v111 := v110 &&& v96
  let v112 := v84 ^^^ v111
  let v113 := ~~~v80
  let v114 := v113 &&& v86
  let v115 := v99 ^^^ v114
  let v116 := ~~~v95
  let v117 := v116 &&& v101
  let v118 := v89 ^^^ v117
  let v119 := ~~~v91
  let v120 := v119 &&& v97
  let v121 := v85 ^^^ v120
  let v122 := ~~~v81
  let v123 := v122 &&& v87
  let v124 := v100 ^^^ v123
  let v125 := ~~~v96
  let v126 := v125 &&& v102
  let v127 := v90 ^^^ v126
  let v128 := ~~~v86
  let v129 := v128 &&& v92
  let v130 := v80 ^^^ v129
  let v131 := ~~~v101
  let v132 := v131 &&& v82
  let v133 := v95 ^^^ v132
  let v134 := ~~~v97
  let v135 := v134 &&& v103
  let v136 := v91 ^^^ v135
  let v137 := ~~~v87
  let v138 := v137 &&& v93
  let v139 := v81 ^^^ v138
  let v140 := ~~~v102
  let v141 := v140 &&& v83
  let v142 := v96 ^^^ v141
  let v143 := ~~~v92
  let v144 := v143 &&& v98
  let v145 := v86 ^^^ v144
  let v146 := ~~~v82
  let v147 := v146 &&& v88
  let v148 := v101 ^^^ v147
  let v149 := ~~~v103
  let v150 := v149 &&& v55
  let v151 := v97 ^^^ v150
  let v152 := ~~~v93
  let v153 := v152 &&& v94
  let v154 := v87 ^^^ v153
  let v155 := ~~~v83
  let v156 := v155 &&& v84
  let v157 := v102 ^^^ v156
  let v158 := ~~~v98
  let v159 := v158 &&& v99
  let v160 := v92 ^^^ v159
  let v161 := ~~~v88
  let v162 := v161 &&& v89
  let v163 := v82 ^^^ v162
  let v164 := ~~~v55
  let v165 := v164 &&& v85
  let v166 := v103 ^^^ v165
  let v167 := ~~~v94
  let v168 := v167 &&& v100
  let v169 := v93 ^^^ v168
  let v170 := ~~~v84
  let v171 := v170 &&& v90
  let v172 := v83 ^^^ v171
  let v173 := ~~~v99
  let v174 := v173 &&& v80
  let v175 := v98 ^^^ v174
  let v176 := ~~~v89
  let v177 := v176 &&& v95
  let v178 := v88 ^^^ v177
  let v179 := v106 ^^^ 0x8000000080008008#64
  fun i =>
    if i == 0 then v179
    else if i == 1 then v121
    else if i == 2 then v136
    else if i == 3 then v151
    else if i == 4 then v166
    else if i == 5 then v109
    else if i == 6 then v124
    else if i == 7 then v139
    else if i == 8 then v154
    else if i == 9 then v169
    else if i == 10 then v112
    else if i == 11 then v127
    else if i == 12 then v142
    else if i == 13 then v157
    else if i == 14 then v172
    else if i == 15 then v115
    else if i == 16 then v130
    else if i == 17 then v145
    else if i == 18 then v160
    else if i == 19 then v175
    else if i == 20 then v118
    else if i == 21 then v133
    else if i == 22 then v148
    else if i == 23 then v163
    else if i == 24 then v178
    else 0#64
end KeccakEngine.Unrolled
