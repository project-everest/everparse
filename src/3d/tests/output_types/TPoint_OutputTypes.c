

typedef _OPOINT* POpoint;



static inline void SetOpointDerefX (_OPOINT* out, uint8_t __v){
    (out)->(x) = __v;;
}




static inline void SetOpointDerefY (_OPOINT* out, uint32_t __v){
    (out)->(y) = __v;;
}




typedef _OTPOINT* POtpoint;



static inline void SetOtpointDerefOz (_OTPOINT* out, uint64_t __v){
    (out)->(oz) = __v;;
}




static inline _OPOINT* GetOtpointDerefOpAddrof (_OTPOINT* out){
    return &((out)->(op));;
}




static inline void SetOtpointDerefOpDotX (_OTPOINT* out, uint8_t __v){
    ((out)->(op)).(x) = __v;;
}




static inline void SetOtpointDerefOpDotY (_OTPOINT* out, uint32_t __v){
    ((out)->(op)).(y) = __v;;
}


