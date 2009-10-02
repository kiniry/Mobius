package java.awt;

public final class JobAttributes$MultipleDocumentHandlingType extends AttributeValue {
    private static final int I_SEPARATE_DOCUMENTS_COLLATED_COPIES = 0;
    private static final int I_SEPARATE_DOCUMENTS_UNCOLLATED_COPIES = 1;
    private static final String[] NAMES = {"separate-documents-collated-copies", "separate-documents-uncollated-copies"};
    public static final JobAttributes$MultipleDocumentHandlingType SEPARATE_DOCUMENTS_COLLATED_COPIES = new JobAttributes$MultipleDocumentHandlingType(I_SEPARATE_DOCUMENTS_COLLATED_COPIES);
    public static final JobAttributes$MultipleDocumentHandlingType SEPARATE_DOCUMENTS_UNCOLLATED_COPIES = new JobAttributes$MultipleDocumentHandlingType(I_SEPARATE_DOCUMENTS_UNCOLLATED_COPIES);
    
    private JobAttributes$MultipleDocumentHandlingType(int type) {
        super(type, NAMES);
    }
}
